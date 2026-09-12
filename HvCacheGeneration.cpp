// C++ port of the cash generation path from the C# MemCrypto remake of
// https://github.com/GoobyCorp/Xbox-360-Crypto/blob/master/MemCrypto.py
// credits = ["tydye81", "teir1plus2", "no-op", "juv", "GoobyCorp"]

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include <windows.h>
#include <bcrypt.h>

#pragma comment(lib, "bcrypt.lib")

namespace fs = std::filesystem;

// ---------------------------------------------------------------------------
// Paths
// ---------------------------------------------------------------------------
static const char* kBinFolder = "bin";
static const char* kKeyFilePath = "bin\\keys.bin";
static const char* kHvDecFilePath = "bin\\hv_dec.bin";
static const char* kHvEncFilePath = "bin\\hv_enc.bin";
static const char* kOutputFolder = "bin\\output";

static constexpr int SRAM_CKSM_PAGE_SIZE = 0x80;
static constexpr int GF2_IV = 0;
static constexpr int GF2_POLY = 0x87;

static std::array<uint8_t, 16> ALL_55_KEY{};
static std::array<uint16_t, 256> GF2_TAB{};

static constexpr uint64_t UINT36_MASK = (1ULL << 36) - 1ULL;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
static void EnsureDefaultDirectories()
{
    for (const char* dir : { kBinFolder, kOutputFolder })
    {
        if (!fs::exists(dir))
        {
            fs::create_directories(dir);
            std::cout << "Created directory: " << dir << "\n";
        }
    }
}

static void EnsureDefaultKeys()
{
    if (!fs::exists(kKeyFilePath))
    {
        std::vector<uint8_t> defaultKeys(48, 0x55);
        std::ofstream out(kKeyFilePath, std::ios::binary);
        out.write(reinterpret_cast<const char*>(defaultKeys.data()),
                  static_cast<std::streamsize>(defaultKeys.size()));
        std::cout << "Created default 555 keys at: " << kKeyFilePath << "\n";
    }
}

static std::vector<uint8_t> ReadFile(const std::string& filename)
{
    std::ifstream in(filename, std::ios::binary | std::ios::ate);
    if (!in)
        throw std::runtime_error("Failed to open file: " + filename);

    const auto size = in.tellg();
    if (size < 0)
        throw std::runtime_error("Failed to get size of file: " + filename);

    std::vector<uint8_t> data(static_cast<size_t>(size));
    in.seekg(0, std::ios::beg);
    if (size > 0)
        in.read(reinterpret_cast<char*>(data.data()), size);
    return data;
}

static void WriteFile(const std::string& filename, const std::vector<uint8_t>& data)
{
    std::ofstream out(filename, std::ios::binary);
    if (!out)
        throw std::runtime_error("Failed to write file: " + filename);
    out.write(reinterpret_cast<const char*>(data.data()),
              static_cast<std::streamsize>(data.size()));
}

static std::string BytesToHex(const uint8_t* data, size_t len)
{
    std::ostringstream oss;
    oss << std::uppercase << std::hex << std::setfill('0');
    for (size_t i = 0; i < len; ++i)
        oss << std::setw(2) << static_cast<unsigned>(data[i]);
    return oss.str();
}

static std::vector<uint8_t> ReadChunk(const std::vector<uint8_t>& data, int offset, int size)
{
    if (offset < 0 || size < 0 ||
        static_cast<size_t>(offset) + static_cast<size_t>(size) > data.size())
    {
        throw std::out_of_range("Requested offset and size exceed the data length.");
    }
    return std::vector<uint8_t>(data.begin() + offset, data.begin() + offset + size);
}

static uint16_t Rotr(uint16_t n, int d, int b)
{
    const int shift = b - d;
    const uint16_t mask = static_cast<uint16_t>((1 << b) - 1);
    uint32_t val = n;
    val = static_cast<uint16_t>(((val >> d) | ((val << shift) & mask)) & 0xFFFF);
    return static_cast<uint16_t>(val);
}

static std::vector<uint8_t> SxorU32(const std::vector<uint8_t>& s1, const std::vector<uint8_t>& s2)
{
    if (s1.size() != s2.size())
        throw std::runtime_error("s1 and s2 must be the same size");

    std::vector<uint8_t> result(s1.size());
    for (size_t i = 0; i + 4 <= s1.size(); i += 4)
    {
        uint32_t a = 0, b = 0;
        std::memcpy(&a, &s1[i], 4);
        std::memcpy(&b, &s2[i], 4);
        const uint32_t c = a ^ b;
        std::memcpy(&result[i], &c, 4);
    }
    return result;
}

static std::vector<uint8_t> SandU32(const std::vector<uint8_t>& s1, const std::vector<uint8_t>& s2)
{
    if (s1.size() != s2.size())
        throw std::runtime_error("s1 and s2 must be the same size");

    std::vector<uint8_t> result(s1.size());
    for (size_t i = 0; i + 4 <= s1.size(); i += 4)
    {
        uint32_t a = 0, b = 0;
        std::memcpy(&a, &s1[i], 4);
        std::memcpy(&b, &s2[i], 4);
        const uint32_t c = a & b;
        std::memcpy(&result[i], &c, 4);
    }
    return result;
}

static std::array<uint16_t, 256> GenerateGf2Table(int iv, int poly)
{
    std::array<uint16_t, 256> tab{};
    for (int i = 0; i < 256; ++i)
    {
        int crc = iv;
        int c = i << 8;
        for (int j = 0; j < 8; ++j)
        {
            if (((crc ^ c) & 0x8000) != 0)
                crc = (crc << 1) ^ poly;
            else
                crc <<= 1;
            c <<= 1;
        }
        tab[static_cast<size_t>(i)] = static_cast<uint16_t>(crc & 0xFFFF);
    }
    return tab;
}

static std::vector<uint8_t> RepeatKey(const std::array<uint8_t, 16>& key, int count)
{
    std::vector<uint8_t> result(static_cast<size_t>(16 * count));
    for (int i = 0; i < count; ++i)
        std::memcpy(result.data() + i * 16, key.data(), 16);
    return result;
}

// ---------------------------------------------------------------------------
// Minimal big-endian style 256-bit integer for tweak math
// limbs[0] = least significant 64 bits
// ---------------------------------------------------------------------------
struct UInt256
{
    uint64_t limbs[4]{};

    static UInt256 FromBigEndian16(const uint8_t* be16)
    {
        UInt256 v;
        for (int i = 0; i < 16; ++i)
        {
            const int bitPos = (15 - i) * 8;
            const int limb = bitPos / 64;
            const int shift = bitPos % 64;
            v.limbs[limb] |= static_cast<uint64_t>(be16[i]) << shift;
        }
        return v;
    }

    UInt256 operator^(const UInt256& o) const
    {
        UInt256 r;
        for (int i = 0; i < 4; ++i)
            r.limbs[i] = limbs[i] ^ o.limbs[i];
        return r;
    }

    UInt256& operator^=(const UInt256& o)
    {
        for (int i = 0; i < 4; ++i)
            limbs[i] ^= o.limbs[i];
        return *this;
    }

    UInt256 operator<<(int n) const
    {
        UInt256 r;
        if (n <= 0)
            return *this;
        if (n >= 256)
            return r;

        const int limbShift = n / 64;
        const int bitShift = n % 64;

        for (int i = 3; i >= 0; --i)
        {
            const int src = i - limbShift;
            if (src < 0)
                continue;

            r.limbs[i] |= limbs[src] << bitShift;
            if (bitShift != 0 && src > 0)
                r.limbs[i] |= limbs[src - 1] >> (64 - bitShift);
        }
        return r;
    }

    UInt256 operator>>(int n) const
    {
        UInt256 r;
        if (n <= 0)
            return *this;
        if (n >= 256)
            return r;

        const int limbShift = n / 64;
        const int bitShift = n % 64;

        for (int i = 0; i < 4; ++i)
        {
            const int src = i + limbShift;
            if (src >= 4)
                continue;

            r.limbs[i] |= limbs[src] >> bitShift;
            if (bitShift != 0 && src + 1 < 4)
                r.limbs[i] |= limbs[src + 1] << (64 - bitShift);
        }
        return r;
    }

    UInt256 operator&(uint64_t mask) const
    {
        UInt256 r = *this;
        r.limbs[0] &= mask;
        r.limbs[1] = 0;
        r.limbs[2] = 0;
        r.limbs[3] = 0;
        return r;
    }

    bool Bit(int i) const
    {
        if (i < 0 || i >= 256)
            return false;
        return ((limbs[i / 64] >> (i % 64)) & 1ULL) != 0;
    }

    // Low 128 bits as big-endian 16 bytes
    std::array<uint8_t, 16> ToBigEndian16() const
    {
        std::array<uint8_t, 16> out{};
        for (int i = 0; i < 16; ++i)
        {
            const int bitPos = (15 - i) * 8;
            const int limb = bitPos / 64;
            const int shift = bitPos % 64;
            out[static_cast<size_t>(i)] =
                static_cast<uint8_t>((limbs[limb] >> shift) & 0xFF);
        }
        return out;
    }

    UInt256 Low128() const
    {
        UInt256 r;
        r.limbs[0] = limbs[0];
        r.limbs[1] = limbs[1];
        return r;
    }
};

// ---------------------------------------------------------------------------
// AES-128 ECB via Windows BCrypt (no padding)
// ---------------------------------------------------------------------------
static std::array<uint8_t, 16> AesEcbTransform(const std::array<uint8_t, 16>& key,
                                               const std::array<uint8_t, 16>& data,
                                               bool encrypt)
{
    BCRYPT_ALG_HANDLE alg = nullptr;
    BCRYPT_KEY_HANDLE keyHandle = nullptr;
    std::array<uint8_t, 16> result{};

    NTSTATUS status = BCryptOpenAlgorithmProvider(&alg, BCRYPT_AES_ALGORITHM, nullptr, 0);
    if (!BCRYPT_SUCCESS(status))
        throw std::runtime_error("BCryptOpenAlgorithmProvider failed");

    status = BCryptSetProperty(alg, BCRYPT_CHAINING_MODE,
                               reinterpret_cast<PUCHAR>(const_cast<wchar_t*>(BCRYPT_CHAIN_MODE_ECB)),
                               sizeof(BCRYPT_CHAIN_MODE_ECB), 0);
    if (!BCRYPT_SUCCESS(status))
    {
        BCryptCloseAlgorithmProvider(alg, 0);
        throw std::runtime_error("BCryptSetProperty chaining mode failed");
    }

    status = BCryptGenerateSymmetricKey(
        alg, &keyHandle, nullptr, 0,
        reinterpret_cast<PUCHAR>(const_cast<uint8_t*>(key.data())),
        static_cast<ULONG>(key.size()), 0);
    if (!BCRYPT_SUCCESS(status))
    {
        BCryptCloseAlgorithmProvider(alg, 0);
        throw std::runtime_error("BCryptGenerateSymmetricKey failed");
    }

    ULONG cbResult = 0;
    if (encrypt)
    {
        status = BCryptEncrypt(keyHandle,
                               reinterpret_cast<PUCHAR>(const_cast<uint8_t*>(data.data())),
                               16, nullptr, nullptr, 0,
                               result.data(), 16, &cbResult, 0);
    }
    else
    {
        status = BCryptDecrypt(keyHandle,
                               reinterpret_cast<PUCHAR>(const_cast<uint8_t*>(data.data())),
                               16, nullptr, nullptr, 0,
                               result.data(), 16, &cbResult, 0);
    }

    BCryptDestroyKey(keyHandle);
    BCryptCloseAlgorithmProvider(alg, 0);

    if (!BCRYPT_SUCCESS(status) || cbResult != 16)
        throw std::runtime_error("AES transform failed");

    return result;
}

// ---------------------------------------------------------------------------
// MemoryCrypto (cash-related subset)
// ---------------------------------------------------------------------------
class MemoryCrypto
{
public:
    std::array<uint8_t, 16> white_key{};
    std::array<uint8_t, 16> aes_key{};
    std::array<uint8_t, 16> hash_key{};

    MemoryCrypto(const std::array<uint8_t, 16>& wkey,
                 const std::array<uint8_t, 16>& akey,
                 const std::array<uint8_t, 16>& hkey)
        : white_key(wkey), aes_key(akey), hash_key(hkey)
    {
    }

    int SramOffsetToHvOffset(int sram_offset) const
    {
        return (sram_offset / 2) * SRAM_CKSM_PAGE_SIZE;
    }

    int SramSizeToHvSize(int sram_size) const
    {
        return SramOffsetToHvOffset(sram_size);
    }

private:
    UInt256 GetTweak1(UInt256 n) const
    {
        uint64_t of = (n >> 128).limbs[0] & UINT36_MASK;
        n = n.Low128();

        int i = 0;
        while (of > 0)
        {
            const int index = static_cast<int>(of & 0xFF);
            if (index >= static_cast<int>(GF2_TAB.size()))
                break;

            UInt256 term;
            term.limbs[0] = GF2_TAB[static_cast<size_t>(index)];
            n ^= (term << (i * 8));
            of >>= 8;
            ++i;
        }
        return n.Low128();
    }

    std::array<uint8_t, 16> GetTweak0(int64_t address) const
    {
        UInt256 key = UInt256::FromBigEndian16(white_key.data());
        UInt256 value = key << 36;
        const int64_t addr = address >> 4;

        for (int i = 0; i < 64; ++i)
        {
            if (((addr >> i) & 1) == 1)
                value ^= (key << i);
        }

        return GetTweak1(value).ToBigEndian16();
    }

    static int64_t FixAddress(int64_t address)
    {
        if (address >= 0 && address <= 0x40000)
            return address | (0x200000000LL * (address / 0x10000));
        return address;
    }

public:
    std::vector<uint8_t> EncryptBlock(const std::vector<uint8_t>& dec_data,
                                      int offset, int size,
                                      int64_t address = 0,
                                      bool offset_is_address = false) const
    {
        if (offset_is_address)
            address = offset;

        auto block = ReadChunk(dec_data, offset, size);
        auto tweak = GetTweak0(address);

        auto xored = SxorU32(block, std::vector<uint8_t>(tweak.begin(), tweak.end()));

        std::array<uint8_t, 16> block16{};
        std::memcpy(block16.data(), xored.data(), 16);

        // Matches C#: EncryptBlock uses AES decrypt transform
        auto enc16 = AesEcbTransform(aes_key, block16, false);
        auto enc_data = std::vector<uint8_t>(enc16.begin(), enc16.end());
        enc_data = SxorU32(enc_data, std::vector<uint8_t>(tweak.begin(), tweak.end()));
        return enc_data;
    }

    std::vector<uint8_t> Encrypt(const std::vector<uint8_t>& hv_data_dec_in,
                                 int offset, int size,
                                 int64_t address = 0,
                                 bool offset_is_address = false) const
    {
        if (offset_is_address)
            address = offset;
        if (size % 16 != 0)
            throw std::runtime_error("Size must be divisible by 16");

        auto hv_data_dec = ReadChunk(hv_data_dec_in, offset, size);
        std::vector<uint8_t> out;
        out.reserve(static_cast<size_t>(size));

        for (int i = 0; i < size; i += 16)
        {
            auto block = EncryptBlock(hv_data_dec, i, 16, FixAddress(address + i), false);
            out.insert(out.end(), block.begin(), block.end());
        }
        return out;
    }

    uint16_t CalcSramChecksum(const std::vector<uint8_t>& data) const
    {
        const int length = static_cast<int>(data.size());
        uint16_t cksm = 0;
        int rot_val = 1;
        for (int i = 0; i < length / 2; ++i)
        {
            const uint16_t v = static_cast<uint16_t>((data[static_cast<size_t>(i) * 2] << 8) |
                                                     data[static_cast<size_t>(i) * 2 + 1]);
            const uint16_t r = Rotr(v, rot_val, 16);
            cksm = static_cast<uint16_t>(cksm ^ r);
            rot_val = ((i + 1) / 4) + 1;
        }
        return static_cast<uint16_t>(cksm & 0xFFFF);
    }

    std::vector<uint8_t> CalcSramChecksums(const std::vector<uint8_t>& hv_data_dec_in,
                                           const std::vector<uint8_t>& hv_data_enc_in,
                                           int offset, int size) const
    {
        if (size % SRAM_CKSM_PAGE_SIZE != 0)
            throw std::runtime_error("Hashes require data divisible by 0x80");

        auto hv_data_dec = ReadChunk(hv_data_dec_in, offset, size);
        auto hv_data_enc = ReadChunk(hv_data_enc_in, offset, size);

        auto mask = RepeatKey(hash_key, static_cast<int>(hv_data_dec.size() / 0x10));
        auto masked = SandU32(hv_data_enc, mask);
        hv_data_dec = SxorU32(masked, hv_data_dec);

        const int num_cksm_pages = size / SRAM_CKSM_PAGE_SIZE;
        std::vector<uint8_t> out;
        out.reserve(static_cast<size_t>(num_cksm_pages) * 2);

        for (int i = 0; i < num_cksm_pages; ++i)
        {
            auto page = ReadChunk(hv_data_dec, i * SRAM_CKSM_PAGE_SIZE, SRAM_CKSM_PAGE_SIZE);
            const uint16_t c = CalcSramChecksum(page);
            // HostToNetworkOrder (big-endian)
            const uint16_t net_c = static_cast<uint16_t>(((c & 0xFF) << 8) | ((c >> 8) & 0xFF));
            out.push_back(static_cast<uint8_t>(net_c & 0xFF));
            out.push_back(static_cast<uint8_t>((net_c >> 8) & 0xFF));
        }
        return out;
    }

    std::vector<uint8_t> CalcSram(const std::vector<uint8_t>& hv_data_dec) const
    {
        auto hv_data_enc = Encrypt(hv_data_dec, 0, 0x40000, 0, false);
        return CalcSramChecksums(hv_data_dec, hv_data_enc, 0, 0x40000);
    }
};

// ---------------------------------------------------------------------------
// Cash generation (non-command; runs on load)
// ---------------------------------------------------------------------------
static void GenerateCash()
{
    const std::string inputFile = kHvDecFilePath;
    const std::string keysFile = kKeyFilePath;
    const std::string outputFolder = kOutputFolder;

    try
    {
        if (!fs::exists(inputFile))
        {
            std::cout << "Error: Input hypervisor file not found at " << inputFile << "\n";
            std::cout << "Expected default path: " << kHvDecFilePath << "\n";
            return;
        }

        std::vector<uint8_t> hv_dec;
        try
        {
            hv_dec = ReadFile(inputFile);
            std::cout << "Successfully read hypervisor file: " << inputFile
                      << " (Size: " << std::hex << std::uppercase << hv_dec.size()
                      << std::dec << " bytes)\n";
            std::cout << "Loaded: hv_dec\n";
        }
        catch (const std::exception& ex)
        {
            std::cout << "Error reading hypervisor file " << inputFile << ": " << ex.what() << "\n";
            return;
        }

        if (hv_dec.size() < 0x40000)
        {
            std::cout << "Error: Hypervisor file must be at least 0x40000 bytes. Current size: 0x"
                      << std::hex << std::uppercase << hv_dec.size() << std::dec << "\n";
            return;
        }

        if (hv_dec.size() % 16 != 0)
        {
            std::cout << "Error: Hypervisor file size must be a multiple of 16. Current size: 0x"
                      << std::hex << std::uppercase << hv_dec.size() << std::dec << "\n";
            return;
        }

        std::array<uint8_t, 16> white_key{};
        std::array<uint8_t, 16> aes_key{};
        std::array<uint8_t, 16> hash_key{};

        if (fs::exists(keysFile))
        {
            try
            {
                auto keys = ReadFile(keysFile);
                std::cout << "Read keys file: " << keysFile
                          << " (Size: " << std::hex << std::uppercase << keys.size()
                          << std::dec << " bytes)\n";

                if (keys.size() >= 0x30)
                {
                    std::memcpy(white_key.data(), keys.data(), 16);
                    std::memcpy(aes_key.data(), keys.data() + 16, 16);
                    std::memcpy(hash_key.data(), keys.data() + 32, 16);
                    std::cout << "Loaded: keys\n";
                }
                else
                {
                    std::cout << "Warning: Keys file " << keysFile << " is too small ("
                              << std::hex << std::uppercase << keys.size() << std::dec
                              << " bytes). Using default 555 keys.\n";
                    white_key = ALL_55_KEY;
                    aes_key = ALL_55_KEY;
                    hash_key = ALL_55_KEY;
                    std::cout << "Loaded: keys (555 default)\n";
                }
            }
            catch (const std::exception& ex)
            {
                std::cout << "Error reading keys file " << keysFile << ": " << ex.what() << "\n";
                std::cout << "Using default 555 keys.\n";
                white_key = ALL_55_KEY;
                aes_key = ALL_55_KEY;
                hash_key = ALL_55_KEY;
                std::cout << "Loaded: keys (555 default)\n";
            }
        }
        else
        {
            std::cout << "Warning: Keys file " << keysFile << " not found. Using default 555 keys.\n";
            white_key = ALL_55_KEY;
            aes_key = ALL_55_KEY;
            hash_key = ALL_55_KEY;
            EnsureDefaultKeys();
            std::cout << "Loaded: keys (555 default)\n";
        }

        std::cout << "Using keys:\n";
        std::cout << "W: " << BytesToHex(white_key.data(), 16) << "\n";
        std::cout << "A: " << BytesToHex(aes_key.data(), 16) << "\n";
        std::cout << "H: " << BytesToHex(hash_key.data(), 16) << "\n";
        std::cout << "\n";

        std::cout << "Processing hypervisor...\n";

        std::cout << "Encrypting hypervisor...\n";
        std::vector<uint8_t> hv_enc;
        {
            MemoryCrypto mem(white_key, aes_key, hash_key);
            hv_enc = mem.Encrypt(hv_dec, 0, static_cast<int>(hv_dec.size()), 0, false);
            std::cout << "Encryption completed.\n";
            std::cout << "Loaded: hv_enc\n";
        }

        // Also mirror encrypted HV into bin\hv_enc.bin for convenience
        WriteFile(kHvEncFilePath, hv_enc);

        std::cout << "Calculating SRAM checksums...\n";
        std::vector<uint8_t> sram;
        {
            MemoryCrypto mem(white_key, aes_key, hash_key);
            sram = mem.CalcSram(hv_dec);
            std::cout << "SRAM checksums calculated.\n";
            std::cout << "Loaded: sram\n";
        }

        if (!fs::exists(outputFolder))
        {
            fs::create_directories(outputFolder);
            std::cout << "Created output folder: " << outputFolder << "\n";
        }

        std::cout << "Writing output files...\n";

        const std::string keysOutputPath = (fs::path(outputFolder) / "keys.bin").string();
        std::vector<uint8_t> keysCombined(48);
        std::memcpy(keysCombined.data(), white_key.data(), 16);
        std::memcpy(keysCombined.data() + 16, aes_key.data(), 16);
        std::memcpy(keysCombined.data() + 32, hash_key.data(), 16);
        WriteFile(keysOutputPath, keysCombined);
        std::cout << "Keys written to: " << keysOutputPath << "\n";

        WriteFile((fs::path(outputFolder) / "HV.dec.bin").string(), hv_dec);
        WriteFile((fs::path(outputFolder) / "HV.enc.bin").string(), hv_enc);
        WriteFile((fs::path(outputFolder) / "sram.bin").string(), sram);

        std::cout << "Cash files generated successfully.\n";
    }
    catch (const std::exception& ex)
    {
        std::cout << "Error processing hypervisor: " << ex.what() << "\n";
    }
}

int main()
{
    ALL_55_KEY.fill(0x55);
    EnsureDefaultDirectories();
    GF2_TAB = GenerateGf2Table(GF2_IV, GF2_POLY);

    std::cout << "Loaded: MemoryCrypto\n";
    std::cout << "Loaded: Cash\n";
    std::cout << "\n";

    GenerateCash();

    std::cout << "Done!\n";
    system("pause");
    return 0;
}
