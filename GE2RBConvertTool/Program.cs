using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;

namespace GE2RBConvertTool
{
    enum OpType { Delete, Insert }

    class Operation
    {
        public long Address { get; set; }
        public OpType Type { get; set; }
        public int Length { get; set; }
        public byte FillValue { get; set; } = 0x00;
    }

    class Program
    {
        // 动态大小
        public static int SAVE_SIZE;
        public static int BODY_SIZE;
        public static int TRAILER_OFFSET;

        // 固定偏移
        public const uint MASK32 = 0xFFFFFFFF;
        public const ulong MASK64 = 0xFFFFFFFFFFFFFFFF;
        public const ulong UNIVERSAL_CONSTANT = 0x8A51891CE32973E4;
        public const int CHKSUM_OFFSET = 0x10;
        public const int EZHASH_OFFSET = 0x14;
        public const int RTCHASH_OFFSET = 0x40;

        // 嵌入式资源名称
        private const string SecureConvRes = "GE2RBConvertTool.SECURE_convent.txt";
        private const string CxxConvRes = "GE2RBConvertTool.CXX__convent.txt";

        static int Main(string[] args)
        {
            if (args.Length == 0 || Directory.Exists(args[0]))
            {
                string folder = args.Length > 0 ? args[0] : Directory.GetCurrentDirectory();
                try
                {
                    CmdConvert(folder);
                    return 0;
                }
                catch (Exception ex)
                {
                    Console.WriteLine($"错误: {ex.Message}");
                    Console.WriteLine("按任意键退出...");
                    Console.ReadKey();
                    return 1;
                }
            }
            else
            {
                Console.WriteLine(@"
噬神者2狂怒解放存档转换工具

用法：将包含 SECURE.BIN 的文件夹拖到此 exe 上，或直接运行并输入文件夹路径。
转换后的存档将保存在原文件夹同级的新目录中（名称含目标平台），原文件不变。

示例：GE2RBConvertTool.exe D:\SaveData
      或直接将文件夹拖到 GE2RBConvertTool.exe 图标上。
");
                Console.WriteLine("按任意键退出...");
                Console.ReadKey();
                return 1;
            }
        }

        // ========== 加密/解密核心 ==========
        static ulong Mul64(uint lo, uint hi, uint m_lo, uint m_hi)
        {
            if (m_hi == 0 && hi == 0)
                return (ulong)lo * m_lo & MASK64;
            ulong a = ((ulong)hi << 32) | lo;
            ulong b = ((ulong)m_hi << 32) | m_lo;
            return (a * b) & MASK64;
        }

        static ulong LcgStep(ulong state)
        {
            uint lo = (uint)(state & MASK32);
            uint hi = (uint)((state >> 32) & MASK32);
            ulong uVar6 = Mul64(lo, hi, 0x01000001, 0);
            uint u6_lo = (uint)(uVar6 & MASK32);
            uint u6_hi = (uint)((uVar6 >> 32) & MASK32);
            uint part_low = (u6_lo * 0x100) & MASK32;
            uint part_high = (((u6_hi << 8) & MASK32) | (u6_lo >> 0x18)) & MASK32;
            ulong concat = ((ulong)part_high << 32) | part_low;
            return ((uVar6 >> 0x10) + concat) & MASK64;
        }

        static float F01F32(uint bits32)
        {
            uint bits = (bits32 & 0x7fffff) | 0x3f800000;
            byte[] bytes = BitConverter.GetBytes(bits);
            if (!BitConverter.IsLittleEndian) Array.Reverse(bytes);
            float val = BitConverter.ToSingle(bytes, 0);
            return val - 1.0f;
        }

        static (int[] fwd, int[] inv, ulong state) GenTable(ulong state)
        {
            int[] fwd = new int[256];
            int[] inv = new int[256];
            List<int> local = Enumerable.Range(0, 256).ToList();
            int remaining = 256;
            int idx = 0;
            for (int i = 0; i < 256; i++)
            {
                state = LcgStep(state);
                float f = F01F32((uint)(state & MASK32));
                float product = f * remaining;
                int pick = (int)product;
                if (pick >= remaining) pick = remaining - 1;
                if (pick < 0) pick = 0;
                int val = local[pick];
                local[pick] = local[remaining - 1];
                fwd[idx] = val;
                inv[val] = idx;
                idx++;
                remaining--;
            }
            return (fwd, inv, state);
        }

        static (uint running, ulong seed) InitState(uint key_lo, uint key_hi)
        {
            ulong key = ((ulong)key_hi << 32) | key_lo;
            ulong lVar1 = LcgStep(key);
            ulong seed = LcgStep(lVar1);
            float f_hi = F01F32((uint)(lVar1 & MASK32));
            float f_lo = F01F32((uint)(seed & MASK32));
            uint part_hi = (uint)((int)(f_hi * 65536.0f) & 0xFFFF);
            uint part_lo = (uint)((int)(f_lo * 65536.0f) & 0xFFFF);
            uint running = ((part_hi << 16) | part_lo) & MASK32;
            return (running, seed);
        }

        static (uint key_lo, uint key_hi) DeriveKey(ulong rtchash)
        {
            ulong combined = (UNIVERSAL_CONSTANT + rtchash) & MASK64;
            return ((uint)(combined & MASK32), (uint)((combined >> 32) & MASK32));
        }

        public static byte[] Decrypt(byte[] ciphertext, uint key_lo, uint key_hi, int length)
        {
            var (state, seed) = InitState(key_lo, key_hi);
            byte[] dest = new byte[length];
            int pos = 0;
            while (pos < length)
            {
                int chunk_len = Math.Min(256, length - pos);
                var (fwd, inv, newSeed) = GenTable(seed);
                seed = newSeed;
                int nwords = ((chunk_len - 1) >> 2) + 1;
                for (int w = 0; w < nwords; w++)
                {
                    int off = pos + w * 4;
                    uint src_word = BitConverter.ToUInt32(ciphertext, off);
                    state = (state ^ src_word) & MASK32;
                    byte[] stateBytes = BitConverter.GetBytes(state);
                    if (!BitConverter.IsLittleEndian) Array.Reverse(stateBytes);
                    Array.Copy(stateBytes, 0, dest, off, 4);
                }
                for (int i = 0; i < chunk_len; i++)
                {
                    int b = dest[pos + i];
                    dest[pos + i] = (byte)((inv[b] - i) & 0xFF);
                }
                pos += chunk_len;
            }
            return dest;
        }

        public static byte[] Encrypt(byte[] plaintext, uint key_lo, uint key_hi, int length)
        {
            var (state, seed) = InitState(key_lo, key_hi);
            byte[] dest = new byte[length];
            int pos = 0;
            while (pos < length)
            {
                int chunk_len = Math.Min(256, length - pos);
                var (fwd, inv, newSeed) = GenTable(seed);
                seed = newSeed;
                int nwords = ((chunk_len - 1) >> 2) + 1;
                byte[] step1 = new byte[nwords * 4];
                for (int i = 0; i < chunk_len; i++)
                {
                    byte p = plaintext[pos + i];
                    step1[i] = (byte)fwd[(p + i) & 0xFF];
                }
                for (int w = 0; w < nwords; w++)
                {
                    int off = w * 4;
                    uint new_state = BitConverter.ToUInt32(step1, off);
                    uint cipher_word = (state ^ new_state) & MASK32;
                    byte[] cipherBytes = BitConverter.GetBytes(cipher_word);
                    if (!BitConverter.IsLittleEndian) Array.Reverse(cipherBytes);
                    Array.Copy(cipherBytes, 0, dest, pos + off, 4);
                    state = new_state;
                }
                pos += chunk_len;
            }
            return dest;
        }

        public static (uint chksum, uint ezhash) ComputeChecksums(byte[] data)
        {
            if (data.Length != SAVE_SIZE)
                throw new ArgumentException($"期望 {SAVE_SIZE} 字节，实际 {data.Length}");

            byte[] work = (byte[])data.Clone();
            int[] zeroOffsets = { CHKSUM_OFFSET, EZHASH_OFFSET, RTCHASH_OFFSET, RTCHASH_OFFSET + 4,
                                  TRAILER_OFFSET, TRAILER_OFFSET + 4 };
            foreach (int off in zeroOffsets)
                Array.Copy(new byte[4], 0, work, off, 4);

            uint chksum = 0;
            uint ezhash = 0;
            foreach (byte b in work)
            {
                chksum = (chksum + b) & MASK32;
                uint prod = (ezhash * 0xE0) & MASK32;
                ezhash = ((prod ^ b) + (prod >> 8)) & MASK32;
            }
            return (chksum, ezhash);
        }

        public static byte[] PatchChecksums(byte[] data)
        {
            var (chksum, ezhash) = ComputeChecksums(data);
            byte[] outData = (byte[])data.Clone();
            byte[] chkBytes = BitConverter.GetBytes(chksum);
            if (!BitConverter.IsLittleEndian) Array.Reverse(chkBytes);
            Array.Copy(chkBytes, 0, outData, CHKSUM_OFFSET, 4);

            byte[] ezBytes = BitConverter.GetBytes(ezhash);
            if (!BitConverter.IsLittleEndian) Array.Reverse(ezBytes);
            Array.Copy(ezBytes, 0, outData, EZHASH_OFFSET, 4);
            return outData;
        }

        // ========== 补丁集成 ==========
        static string[] ReadEmbeddedResource(string resourceName)
        {
            var assembly = Assembly.GetExecutingAssembly();
            using (var stream = assembly.GetManifestResourceStream(resourceName))
            {
                if (stream == null)
                    throw new Exception($"嵌入式资源 {resourceName} 未找到。请确保文件已添加为嵌入资源。");
                using (var reader = new StreamReader(stream))
                {
                    return reader.ReadToEnd().Split(new[] { "\r\n", "\r", "\n" }, StringSplitOptions.RemoveEmptyEntries);
                }
            }
        }

        static List<Operation> LoadOperations(string[] lines)
        {
            var ops = new List<Operation>();
            foreach (string line in lines)
            {
                string trimmed = line.Trim();
                if (string.IsNullOrEmpty(trimmed) || trimmed.StartsWith("#")) continue;

                string[] parts = trimmed.Split(',');
                if (parts.Length < 3) continue;

                try
                {
                    var op = new Operation();
                    string addrStr = parts[0].Trim();
                    op.Address = addrStr.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ?
                        Convert.ToInt64(addrStr, 16) : long.Parse(addrStr);

                    string type = parts[1].Trim().ToUpper();
                    if (type == "D") op.Type = OpType.Delete;
                    else if (type == "I") op.Type = OpType.Insert;
                    else throw new Exception($"未知类型: {type}");

                    string lenStr = parts[2].Trim();
                    op.Length = lenStr.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ?
                        Convert.ToInt32(lenStr, 16) : int.Parse(lenStr);

                    if (parts.Length >= 4 && !string.IsNullOrEmpty(parts[3]))
                    {
                        string valStr = parts[3].Trim();
                        op.FillValue = valStr.StartsWith("0x", StringComparison.OrdinalIgnoreCase) ?
                            Convert.ToByte(valStr, 16) : byte.Parse(valStr);
                    }
                    ops.Add(op);
                }
                catch { /* 忽略解析错误 */ }
            }
            return ops;
        }

        static byte[] ApplyPatch(byte[] data, string[] lines, bool reverse)
        {
            var operations = LoadOperations(lines);
            if (operations.Count == 0)
                throw new Exception("未找到有效操作");

            if (reverse)
                foreach (var op in operations)
                    op.Type = (op.Type == OpType.Delete) ? OpType.Insert : OpType.Delete;

            var sorted = reverse ?
                operations.OrderBy(o => o.Address).ToList() :
                operations.OrderByDescending(o => o.Address).ToList();

            using (var ms = new MemoryStream())
            {
                ms.Write(data, 0, data.Length);
                ms.Position = 0;

                foreach (var op in sorted)
                {
                    if (op.Address < 0 || op.Address > ms.Length) continue;

                    switch (op.Type)
                    {
                        case OpType.Delete:
                            int delLen = (int)Math.Min(op.Length, ms.Length - op.Address);
                            if (delLen <= 0) break;
                            byte[] buffer = new byte[ms.Length - op.Address - delLen];
                            ms.Position = op.Address + delLen;
                            ms.Read(buffer, 0, buffer.Length);
                            ms.Position = op.Address;
                            ms.Write(buffer, 0, buffer.Length);
                            ms.SetLength(ms.Length - delLen);
                            break;
                        case OpType.Insert:
                            byte[] insertData = Enumerable.Repeat(op.FillValue, op.Length).ToArray();
                            byte[] tail = new byte[ms.Length - op.Address];
                            ms.Position = op.Address;
                            ms.Read(tail, 0, tail.Length);
                            ms.Position = op.Address;
                            ms.Write(insertData, 0, insertData.Length);
                            ms.Write(tail, 0, tail.Length);
                            break;
                    }
                }
                return ms.ToArray();
            }
        }

        // ========== 文件夹复制 ==========
        static void CopyDirectory(string sourceDir, string targetDir)
        {
            Directory.CreateDirectory(targetDir);
            foreach (string file in Directory.GetFiles(sourceDir))
            {
                string dest = Path.Combine(targetDir, Path.GetFileName(file));
                File.Copy(file, dest, true);
            }
            foreach (string subDir in Directory.GetDirectories(sourceDir))
            {
                string destSub = Path.Combine(targetDir, Path.GetFileName(subDir));
                CopyDirectory(subDir, destSub);
            }
        }

        // ========== 批量转换 ==========
        static void CmdConvert(string inputFolder)
        {
            if (!Directory.Exists(inputFolder))
                throw new DirectoryNotFoundException($"文件夹不存在: {inputFolder}");

            string securePath = Path.Combine(inputFolder, "SECURE.BIN");
            if (!File.Exists(securePath))
                throw new FileNotFoundException("在文件夹中未找到 SECURE.BIN");

            // 判断平台（基于原文件大小）
            long fileSize = new FileInfo(securePath).Length;
            bool isSteam;
            if (fileSize == 0x90050) isSteam = true;
            else if (fileSize == 0x80050) isSteam = false;
            else
                throw new Exception($"未知存档大小 0x{fileSize:X}，期望 0x90050 (Steam) 或 0x80050 (PS)");

            string sourcePlatform = isSteam ? "Steam" : "PS";
            string targetPlatform = isSteam ? "PS" : "Steam";
            Console.WriteLine($"检测到 {sourcePlatform} 存档，将转换为 {targetPlatform}。");

            // 创建输出文件夹（名称包含目标平台）
            string parent = Path.GetDirectoryName(inputFolder);
            string baseName = Path.GetFileName(inputFolder.TrimEnd(Path.DirectorySeparatorChar));
            string outputFolder = Path.Combine(parent, $"{baseName}_converted_{targetPlatform}");

            if (Directory.Exists(outputFolder))
                Directory.Delete(outputFolder, true);
            Console.WriteLine($"创建输出目录: {outputFolder}");

            // 复制整个文件夹到输出目录
            CopyDirectory(inputFolder, outputFolder);
            Console.WriteLine("复制文件完成。");

            // 获取输出文件夹中的文件路径
            string outSecure = Path.Combine(outputFolder, "SECURE.BIN");

            // 读取原文件（用于解密，但转换在输出目录操作）
            byte[] ciphertext = File.ReadAllBytes(securePath);
            byte[] trailer = ciphertext.Skip(ciphertext.Length - 8).ToArray();
            ulong rtchash = BitConverter.ToUInt64(trailer, 0);
            var (key_lo, key_hi) = DeriveKey(rtchash);
            int body_len = ciphertext.Length - 8;
            byte[] plainBody = Decrypt(ciphertext.Take(body_len).ToArray(), key_lo, key_hi, body_len);
            byte[] plainFull = new byte[plainBody.Length + 8];
            Array.Copy(plainBody, plainFull, plainBody.Length);
            Array.Copy(trailer, 0, plainFull, plainBody.Length, 8);

            // 加载转换表（从嵌入资源）
            string[] secureLines = ReadEmbeddedResource(SecureConvRes);
            string[] cxxLines = ReadEmbeddedResource(CxxConvRes);

            bool reverse = !isSteam; // 从Steam→PS不需要反向，从PS→Steam需要反向
            byte[] patched = ApplyPatch(plainFull, secureLines, reverse);

            // 修正校验和并加密
            SAVE_SIZE = patched.Length;
            BODY_SIZE = SAVE_SIZE - 8;
            TRAILER_OFFSET = BODY_SIZE;
            byte[] fixedPlain = PatchChecksums(patched);

            byte[] rtchashNewBytes = new byte[8];
            Array.Copy(fixedPlain, RTCHASH_OFFSET, rtchashNewBytes, 0, 8);
            ulong rtchashNew = BitConverter.ToUInt64(rtchashNewBytes, 0);
            var (key_lo_new, key_hi_new) = DeriveKey(rtchashNew);

            byte[] bodyToEncrypt = fixedPlain.Take(BODY_SIZE).ToArray();
            byte[] encryptedBody = Encrypt(bodyToEncrypt, key_lo_new, key_hi_new, BODY_SIZE);
            byte[] newCipher = new byte[encryptedBody.Length + 8];
            Array.Copy(encryptedBody, newCipher, encryptedBody.Length);
            Array.Copy(rtchashNewBytes, 0, newCipher, encryptedBody.Length, 8);

            File.WriteAllBytes(outSecure, newCipher);
            Console.WriteLine("SECURE.BIN 转换完成。");

            // 处理角色卡片
            var cardFiles = Directory.GetFiles(outputFolder, "C*.BIN")
                                     .Where(f => Path.GetFileName(f) != "SECURE.BIN")
                                     .ToList();
            foreach (string card in cardFiles)
            {
                byte[] cardData = File.ReadAllBytes(card);
                byte[] patchedCard = ApplyPatch(cardData, cxxLines, reverse);
                File.WriteAllBytes(card, patchedCard);
                Console.WriteLine($"处理 {Path.GetFileName(card)} 完成。");
            }

            Console.WriteLine($"\n全部转换完成！结果已保存至: {outputFolder}");
            Console.WriteLine($"原平台: {sourcePlatform}  →  目标平台: {targetPlatform}");
            Console.WriteLine();
            Console.WriteLine("当前工具无法正常将ps平台的角色卡片正常移植至steam平台。");
            Console.WriteLine("steam平台的角色卡片可正常移植至ps 平台。");
            Console.WriteLine("感谢使用噬神者2狂怒解放存档转换工具，");
            Console.WriteLine("本工具为清羽？（Qingyu510）制作");
            // 等待用户按键，保留窗口
            Console.WriteLine("\n按任意键退出...");
            Console.ReadKey();
        }
    }
}