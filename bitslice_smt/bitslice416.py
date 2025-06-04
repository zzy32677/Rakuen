import z3

def manual_popcount(bv):
    # 计算位向量的汉明重量（1的个数）
    bitlen = bv.size()
    count = z3.BitVecVal(0, bitlen)
    for i in range(bv.size()):
        bit = z3.Extract(i, i, bv)
        count = count + z3.ZeroExt(bitlen-1, bit)
    return count
def bitwise_xor_all(bitvec_expr):
    """
    计算 Z3 比特向量所有位的异或结果。

    Args:
        bitvec_expr (z3.BitVecRef): 要计算异或的 Z3 比特向量表达式。

    Returns:
        z3.BitVecRef: 1位宽的 Z3 比特向量表达式，表示所有位的异或结果。
                      如果位宽为 0，则返回 0。
    """
    bit_width = bitvec_expr.size()

    if bit_width == 0:
        return z3.BitVecVal(0, 1) # 空比特向量的异或结果定义为 0

    # 提取第一位作为初始异或结果
    result_xor = z3.Extract(0, 0, bitvec_expr) # 1位宽的比特向量

    # 从第二位开始遍历并进行异或
    for i in range(1, bit_width):
        current_bit = z3.Extract(i, i, bitvec_expr) # 提取当前位 (1位宽)
        result_xor = result_xor ^ current_bit # 累积异或

    return result_xor

def constrain_bitwise_or_nonzero(bitvec_list):
    """
    约束一个 Z3 比特向量列表的所有元素的按位或结果非零。

    Args:
        bitvec_list (list): 包含 Z3 比特向量表达式的列表。

    Returns:
        z3.BoolRef: 表示按位或非零的 Z3 布尔表达式。
    """
    if not bitvec_list:
        # 如果列表为空，无法进行或操作，根据语境决定如何处理。
        # 这里，如果列表为空，我们可以认为它总是满足“非零”条件，
        # 因为没有比特向量可以“或”出全零。或者返回 False 表达无意义。
        # 对于“或起来非零”，空列表返回 False 更合理，因为没有比特为1。
        print("警告: 输入比特向量列表为空。或运算结果将为 0。")
        return False # 或者 simplify(False)
    
    # 确保所有比特向量的位宽一致，这是按位或操作的前提
    first_bit_width = bitvec_list[0].size()
    for bv in bitvec_list:
        if bv.size() != first_bit_width:
            raise ValueError("列表中所有比特向量的位宽必须一致才能进行按位或操作。")

    # 初始化或结果为列表中的第一个比特向量
    # 如果要避免空列表问题，并确保结果的位宽正确，也可以初始化为零向量
    # 例如：result_or = BitVecVal(0, first_bit_width)
    result_or = bitvec_list[0] 

    # 遍历其余比特向量并进行累积按位或
    for i in range(1, len(bitvec_list)):
        result_or = result_or | bitvec_list[i]
    
    # 约束最终的按位或结果不等于全零向量
    zero_val = z3.BitVecVal(0, first_bit_width)
    return result_or != zero_val

def bitslice(bitlen,slicenum,rotnum,branch_number):
    # 创建Z3求解器
    solver = z3.Solver()
    z3.set_param('parallel.enable', True)
    z3.set_param('verbose', 15)
    z3.set_param('parallel.threads', 4)

    x = [[z3.BitVec(f'x_{i}_{j}', bitlen) for j in range(slicenum)] for i in range(slicenum)]
    matrix_input = [z3.BitVec(f'matrix_input_{i}', bitlen) for i in range(slicenum)]
    
    output = [0 for _ in range(slicenum)]
    for i in range(slicenum):
        ans = []
        for j in range(bitlen):
            temp = []
            for k in range(slicenum):
                temp.append(z3.RotateLeft(x[i][k], j) & matrix_input[k])
            ans.append(bitwise_xor_all(z3.Concat(*temp)))
        output[i] = z3.Concat(*ans)

    if rotnum > 0:
        solver.add(manual_popcount(z3.Concat(*x[0]))+manual_popcount(z3.Concat(*x[1]))+manual_popcount(z3.Concat(*x[2]))+manual_popcount(z3.Concat(*x[3])) <= rotnum + 4)
    solver.add(z3.ForAll(matrix_input,  z3.Implies(constrain_bitwise_or_nonzero(matrix_input), manual_popcount(z3.Concat(*output)) + manual_popcount(z3.Concat(*matrix_input)) >= branch_number)))

    # 检查可满足性
    sat = solver.check()
    print("情况:", sat)
    if sat == z3.sat:
        model = solver.model()
        print(f"找到解:")
        for i in range(len(x)):
            for j in range(len(x[i])):
                val = model[x[i][j]].as_long()
                print(f"x[{i}][{j}] = {val:0{bitlen}b}")
    else:
        print("无解")

bitlen = 64
slicenum = 4
rotnum = -1
branch_number = 13
bitslice(bitlen, slicenum, rotnum, branch_number)