import networkx as nx

from collections import defaultdict

import re
import sympy
from sympy import symbols
from sympy.logic.boolalg import to_dnf
from sympy.parsing.sympy_parser import parse_expr
from sympy.parsing.sympy_parser import standard_transformations, implicit_multiplication_application
from collections import Counter

import re
from collections import Counter, defaultdict
import sympy
from sympy import symbols, simplify_logic
from sympy.parsing.sympy_parser import (
    parse_expr, standard_transformations, implicit_multiplication_application
)

# Chèn dấu * giữa các biến viết liền nhau: AB → A*B
def insert_multiplication(expr):
    return re.sub(r'(?<=[A-Za-z])(?=[A-Za-z])', '*', expr)

# Gom nhóm các hạng tử giống nhau
from itertools import combinations

def deep_group_terms_sorted(expr):
    if isinstance(expr, (sympy.Symbol, sympy.Not)):
        return expr

    terms = list(expr.args) if isinstance(expr, sympy.Or) else [expr]
    term_sets = []
    for t in terms:
        if isinstance(t, sympy.And):
            term_sets.append(set(t.args))
        else:
            term_sets.append({t})

    used = [False] * len(terms)
    final_exprs = []

    for size in range(len(term_sets), 1, -1):  # Bắt đầu từ nhóm lớn nhất
        for group_indices in combinations(range(len(term_sets)), size):
            if any(used[i] for i in group_indices):
                continue
            group_sets = [term_sets[i] for i in group_indices]
            common = set.intersection(*group_sets)
            if common:
                remainders = [s - common for s in group_sets if s - common]
                common = sorted(common, key=str)
                or_part = sympy.Or(*[
                    sympy.And(*sorted(r, key=str)) if len(r) > 1 else list(r)[0]
                    for r in remainders
                ])
                and_part = sympy.And(*(common + [or_part]))
                final_exprs.append(and_part)
                for i in group_indices:
                    used[i] = True

    # Xử lý các số hạng chưa được nhóm
    for i in range(len(term_sets)):
        if not used[i]:
            sorted_term = sorted(term_sets[i], key=str)
            final_exprs.append(sympy.And(*sorted_term) if len(sorted_term) > 1 else sorted_term[0])
            used[i] = True

    final_exprs = sorted(final_exprs, key=lambda x: str(x))
    return sympy.Or(*final_exprs) if len(final_exprs) > 1 else final_exprs[0]
#Đổi tên lại cho Var_mapping
def restore_var_mapping_full(var_mapping, rename_map):
    # Đảo ngược rename_map: new_name → original_name
    reversed_map = {v: k.split('#')[0] for k, v in rename_map.items()}
    
    restored_mapping = {}
    for node, var in var_mapping.items():
        # Khôi phục tên biến nếu nó từng bị đổi
        original_var = reversed_map.get(var, var)
        
        # Nếu bản thân node (ví dụ: D0) chứa tên bị đổi, thì cũng phải đổi lại key
        for new_name, old_name in reversed_map.items():
            if node.startswith(new_name):
                node = node.replace(new_name, old_name, 1)
                break
        
        restored_mapping[node] = original_var
    return restored_mapping
# Sắp xếp biểu thức lại cho đẹp
def sort_terms_alphabetically(expr_str):
    all_vars = set(re.findall(r'[A-Za-z]', expr_str))
    symbols_dict = {v: symbols(v) for v in all_vars}

    expr = parse_expr(expr_str.replace('|', '+').replace('&', '*'), local_dict=symbols_dict, evaluate=False)

    if isinstance(expr, sympy.Or):
        terms = list(expr.args)
    else:
        terms = [expr]

    def term_to_sorted_str(term):
        if isinstance(term, sympy.And):
            factors = sorted(term.args, key=lambda x: str(x))
            return '*'.join(str(f) for f in factors)
        else:
            return str(term)

    sorted_terms = sorted(terms, key=term_to_sorted_str)
    return '+'.join(term_to_sorted_str(t) for t in sorted_terms)

# Phân tích biểu thức để kiểm tra khả năng rút gọn
import sympy
from sympy.parsing.sympy_parser import parse_expr
from collections import defaultdict

def should_simplify(expr,expr_str):
    var_counts = defaultdict(int)
    has_negation = False

    def traverse(e):
        nonlocal has_negation
        if isinstance(e, sympy.Symbol):
            var_counts[str(e)] += 1
        elif isinstance(e, sympy.Not):
            arg = e.args[0]
            has_negation = True
            if isinstance(arg, sympy.Symbol):
                var_counts[str(arg)] += 1
            else:
                traverse(arg)
        else:
            for arg in e.args:
                traverse(arg)

    traverse(expr)

    if has_negation:
        return True

    for count in var_counts.values():
        if count > 1:
            return True

    variables = re.findall(r'[A-Za-z]', expr_str)
    if (len(variables) != len(set(variables))):
        return True

    return False

#Đổi tên biến bù, đổi tên biến bị trùng lặp
from sympy import Symbol
from collections import Counter, defaultdict
import sympy
import string

def sanitize_expression_variables(expr):
    used_vars = set(str(s) for s in expr.atoms(sympy.Symbol))
    rename_map = {}

    # Biến phủ định: Z → Y → X → ...
    negated_candidates = list(reversed(string.ascii_uppercase))
    negated_idx = 0

    # Biến trùng lặp: A → B → C → ...
    duplicate_candidates = list(string.ascii_uppercase)
    duplicate_idx = 0

    def get_next_negated_var():
        nonlocal negated_idx
        while negated_idx < len(negated_candidates):
            v = negated_candidates[negated_idx]
            negated_idx += 1
            if v not in used_vars:
                used_vars.add(v)
                return v
        raise Exception("Ran out of negated variable names.")

    def get_next_duplicate_var():
        nonlocal duplicate_idx
        while duplicate_idx < len(duplicate_candidates):
            v = duplicate_candidates[duplicate_idx]
            duplicate_idx += 1
            if v not in used_vars:
                used_vars.add(v)
                return v
        raise Exception("Ran out of duplicate variable names.")

    # 1. Đổi trực tiếp từng ~A (không dùng xreplace)
    negated_counts = defaultdict(int)

    def replace_negations(e):
        if isinstance(e, sympy.Not):
            inner = e.args[0]
            if isinstance(inner, sympy.Symbol):
                negated_counts[inner] += 1
                key = f'~{inner}#{negated_counts[inner]}'
                new_var = get_next_negated_var()
                rename_map[key] = new_var
                return Symbol(new_var)
            else:
                return sympy.Not(replace_negations(inner))
        elif isinstance(e, sympy.Symbol):
            return e
        else:
            return e.func(*[replace_negations(arg) for arg in e.args])

    expr = replace_negations(expr)

    # 2. Đổi tên các biến trùng lặp
    var_counter = Counter(str(s) for s in expr.atoms(sympy.Symbol))
    seen = defaultdict(int)

    def replace_duplicates(e):
        if isinstance(e, sympy.Symbol):
            name = str(e)
            seen[name] += 1
            if seen[name] > 1:
                new_var = get_next_duplicate_var()
                rename_map[f"{name}#{seen[name]}"] = new_var
                return Symbol(new_var)
            else:
                return e
        elif isinstance(e, sympy.Not):
            return sympy.Not(replace_duplicates(e.args[0]))
        else:
            return e.func(*[replace_duplicates(arg) for arg in e.args])

    expr = replace_duplicates(expr)
    return expr, rename_map



# Rút gọn chính
def simplify_expression(expr_str):
    if '=' in expr_str:
        lhs, rhs = expr_str.split('=')
        lhs = lhs.strip()
        rhs = rhs.strip()
        has_lhs = True
    else:
        lhs = 'Y'
        rhs = expr_str.strip()
        has_lhs = False

    rhs = insert_multiplication(rhs)

    # Biến và từ điển cho sympy
    var_names = set(re.findall(r'[A-Za-z]', rhs))
    symbols_dict = {v: symbols(v) for v in var_names}

    rhs_logic = rhs.replace('+', '|').replace('*', '&').replace('~', '~')
    transformations = standard_transformations + (implicit_multiplication_application,)
    expr = parse_expr(rhs_logic, local_dict=symbols_dict, transformations=transformations, evaluate=False)
    if not should_simplify(expr,expr_str):
        # Không cần rút gọn
        rename_map = {}
        original = rhs.replace('&', '*').replace('|', '+').replace(' ', '')
        return f"{lhs} = {original}" if has_lhs else original, rename_map
    # Rút gọn bằng luật Boolean
    simplified = simplify_logic(expr, form='dnf')
    grouped_expr = deep_group_terms_sorted(simplified)
# Thay thế biến phủ định bằng tên biến mới

    renamed_expr, rename_map = sanitize_expression_variables(grouped_expr)

    output_expr = str(renamed_expr).replace('&', '*').replace('|', '+').replace(' ', '')
    sorted_output_expr = sort_terms_alphabetically(output_expr)

    return f"{lhs} = {sorted_output_expr}" if has_lhs else sorted_output_expr, rename_map


def tokenize_expression(expression):
    # Tách thành list gồm biến (A0, B1) và toán tử (+, *, (, ))
    return re.findall(r'[A-Za-z]\d*|[+*()]', expression)


def rename_duplicate_variables(expr):
    tokens = tokenize_expression(expr)  # Tách ra từng biến + toán tử
    var_count = defaultdict(int)
    new_tokens = []
    var_mapping = {}

    for token in tokens:
        if re.match(r'[A-Za-z]', token):  # là biến
            new_var = f"{token}{var_count[token]}"
            new_tokens.append(new_var)
            var_mapping[new_var] = token
            var_count[token] += 1
        else:
            new_tokens.append(token)

    new_expr = ''.join(new_tokens)
    return new_expr, var_mapping



#xác định độ ưu tiên (precedence) của toán tử trong biểu thức toán học hoặc logic.
def precedence(operator):
    if operator == '+':
        return 1   # độ ưu tiên thấp (cộng OR)
    elif operator == '*':
        return 2   # độ ưu tiên cao hơn (nhân AND)
    else:
        return 0   # mặc định hoặc toán tử không hợp lệ

#ghép hai toán hạng với một toán tử thành biểu thức dạng chuỗi, ví dụ như 'A+B' hoặc 'A*B'
def apply_operator(operand1, operand2, operator, q):
    expression = str(operand1) + str(operator) + str(operand2)
    # q.append(expression)  # bật lại nếu cần ghi nhận biểu thức
    return expression

#đảo ngược dấu
def invert_logic_operator(operand1, operand2, operator):
    if operator == '+':
        return str(operand1) + '*' + str(operand2) #nếu operator = "+" sẽ đổi thành "*"
    else:
        return str(operand1) + '+' + str(operand2) #nếu operator = "*" sẽ đổi thành "+"

#hàm này nhận biểu thức trung tố (infix) như "A+B*C" và tính toán ngược toán tử.
def evaluate_expression_inv(expression, q):
    operand_stack = []
    operator_stack = []
    tokens = tokenize_expression(expression)
    
    for token in tokens:
        if re.match(r'[A-Za-z]\d*', token):  # là biến
            operand_stack.append(token)
        elif token in '+*':
            while operator_stack and precedence(operator_stack[-1]) >= precedence(token):
                operator = operator_stack.pop()
                operand2 = operand_stack.pop()
                operand1 = operand_stack.pop()
                result = invert_logic_operator(operand1, operand2, operator)
                q.append(result)
                operand_stack.append(result)
            operator_stack.append(token)
        elif token == '(':
            operator_stack.append(token)
        elif token == ')':
            while operator_stack[-1] != '(':
                operator = operator_stack.pop()
                operand2 = operand_stack.pop()
                operand1 = operand_stack.pop()
                result = invert_logic_operator(operand1, operand2, operator)
                q.append(result)
                operand_stack.append(result)
            operator_stack.pop()
    while operator_stack:
        operator = operator_stack.pop()
        operand2 = operand_stack.pop()
        operand1 = operand_stack.pop()
        result = invert_logic_operator(operand1, operand2, operator)
        q.append(result)
        operand_stack.append(result)
    
    return operand_stack.pop()


#chuyển và tính toán biểu thức trung tố (infix) – ví dụ "A+B*C" – thành biểu thức hậu tố hoặc cây biểu thức, lưu từng bước vào danh sách q.
def evaluate_expression(expression, q):
    operand_stack = []
    operator_stack = []
    tokens = tokenize_expression(expression)
    
    for token in tokens:
        if re.match(r'[A-Za-z]\d*', token):  # là biến
            operand_stack.append(token)
        elif token in '+*':
            while operator_stack and precedence(operator_stack[-1]) >= precedence(token):
                operator = operator_stack.pop()
                operand2 = operand_stack.pop()
                operand1 = operand_stack.pop()
                result = apply_operator(operand1, operand2, operator, q)
                q.append(result)
                operand_stack.append(result)
            operator_stack.append(token)
        elif token == '(':
            operator_stack.append(token)
        elif token == ')':
            while operator_stack[-1] != '(':
                operator = operator_stack.pop()
                operand2 = operand_stack.pop()
                operand1 = operand_stack.pop()
                result = apply_operator(operand1, operand2, operator, q)
                q.append(result)
                operand_stack.append(result)
            operator_stack.pop()
    while operator_stack:
        operator = operator_stack.pop()
        operand2 = operand_stack.pop()
        operand1 = operand_stack.pop()
        result = apply_operator(operand1, operand2, operator, q)
        q.append(result)
        operand_stack.append(result)
    
    return operand_stack.pop()


#Loại bỏ chuỗi expression2 khỏi expression1, theo thứ tự xuất hiện.
def subtract_expressions(expression1, expression2):     #subtract_expressions("A+(B*C)", "B*C"), duyệt tới B*C khớp => eresult = "A+()".
    i = 0               #chỉ số cho expression1
    j = 0               #chỉ số cho expression2
    result = ''         #chuỗi kết quả sau khi trừ
    while i < len(expression1):
        if(expression1[i] != expression2[j]):
            result += expression1[i]
            i += 1
        else:
            i += 1
            j += 1
        if j == len(expression2): break
    while i < len(expression1):
        result += expression1[i]
        i += 1
    
    return result

#Tìm phần giao (chuỗi con chung, theo thứ tự) giữa expression1 và expression2, bắt đầu từ trái sang phải.
def intersection_expressions(expression1, expression2): #intersection_expressions("A+(B*C)", "B*C"), => result = B*C.
    i = 0
    j = 0
    result =''
    while i < len(expression1):
        if(expression1[i] == expression2[j]):
            result += expression1[i]
            i += 1
            j += 1
        else: i += 1
        if j == len(expression2): break
#    if not result: return 0
    return result

#Kiểm tra xem các phần tử (trong inter_arr) có nối tiếp hợp lệ không, với phần tử đang xét là token, trong đồ thị g.
def check_serial_connected(g, token, inter_arr):
    if len(inter_arr) == 0:
        return True
    arr1 = [0] * len(inter_arr)
    arr2 = [0] * len(inter_arr)
    i = 0
    j = 0
    #chia mảng ra làm arr1 và arr2
    while(1):
        if inter_arr[i] == 0:
            i += 1
            break
        arr1[i] = inter_arr[i]
        i += 1
    while i < len(inter_arr):
        if inter_arr[i] == 0:
            break;
        arr2[j] = inter_arr[i]
        i += 1
        j += 1
    i = 0
    j = 0
    #nếu chỉ có 1 mảng arr1
    if arr2[0] == 0:
        n1_s = token + 'S'
        n1_d = token + 'D'
        while i < len(arr1) - 1:
            if arr1[i] == 0: break
            n2_s = arr1[i] + 'S'
            n2_d = arr1[i] + 'D'
            if(n1_s, n2_d) in g.edges():        #Nếu tồn tại một cạnh trong đồ thị g nối từ n1_s đến n2_d
                return False
            if(n1_d, n2_s) in g.edges():
                return False
            i += 1
        return True
    #nếu có 2 mảng arr1 và arr2
    else:
        while i < len(arr1):
            if arr1[i] == 0: break
            n1_s = arr1[i] + 'S'
            n1_d = arr1[i] + 'D'
            j = 0
            while j < len(arr2):
                if arr2[j] == 0:
                    break
                n2_s = arr2[j] + 'S'
                n2_d = arr2[j] + 'D'
                if (n1_s, n2_d) in g.edges():
                    return False
                if(n1_d, n2_s) in g.edges():
                    return False
                j += 1
            i += 1
        return True
 
#Kiểm tra xem các phần tử (trong inter_arr) có song song hợp lệ không, với phần tử đang xét là k, trong đồ thị g.   
def checking_parallel_connected(g, k, inter_arr):
    if len(inter_arr) == 0:
        return True
    arr1 = []
    arr2 = []
    i = 0
    j = 0
    while(1):
        if inter_arr[i] == 0:
            i += 1
            break
        arr1.append(inter_arr[i])
        i += 1
    while i < len(inter_arr):
        if inter_arr[i] == 0: break
        arr2.append(inter_arr[i])
        i += 1
        j += 1
    i = 0
    j = 0
    if len(arr2) == 0:
        while i < len(arr1) - 1:
            n1 = arr1[i] + k
            j = i + 1
            while j < len(arr1):
                n2 = arr1[j] + k
                if(n1, n2) in g.edges():
                    return False
                j += 1
        return True
    else:
        while i < len(arr1):
            n1 = arr1[i] + k
            j = 0
            while j < len(arr2):
                n2 = arr2[j] + k
                if (n1, n2) in g.edges():
                    return False
                j += 1
            i += 1
        return True
    
#tạo một transistor mới trong đồ thị g   
def create_node(g, node):
    g.add_node(node + 'S')
    g.add_node(node + 'D')
    g.add_edge(node + 'S', node + 'D')  # transistor độc lập


#nối hai transistor chạy song song trong một mạch transistor bằng cách kết nối chân cùng loại (S ↔ S, D ↔ D) của hai transistor lại với nhau.
def add_edge_parallel_1(g, node1, node2):
    n1 = node1 + 'S'
    n2 = node1 + 'D'
    n3 = node2 + 'S'
    n4 = node2 + 'D'
    g.add_edge(n1, n3)
    g.add_edge(n2, n4)
    
#nối tiếp hai transistor trong đồ thị mạch g.
def add_edge_serial_1(g, node1, node2, inter_arr, mode):
    n1 = node1 + 'S'
    n2 = node1 + 'D'
    n3 = node2 + 'S'
    n4 = node2 + 'D'
    if mode == 0:
        g.add_edge(n3, n2)
    elif mode == 1:
        arr = [node1, 0, node2, 0];
        if check_serial_connected(g, ' ',arr) == True:
            g.add_edge(n3, n2)

#nối tiếp thêm một transistor với các transistor khác trong mạch, dựa trên mức độ kết nối (degree) của các nút (nodes) trong đồ thị.
def add_edge_serial_2(g, node, inter_arr, mode):
    n1 = node + 'S'
    n2 = node + 'D'
    v = 0
    i = j = 0

    f = g.copy()  # Tạo đồ thị trung gian
    for nodee in list(f.nodes()):
        if nodee.endswith('D'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A

            for neighbor in f.neighbors(nodee):
                if neighbor.endswith('S'):
                    if neighbor[:-1] != base_node:
                        # Nếu *S nối với *D nhưng khác gốc => xóa node *D
                        f.remove_node(nodee)
                        break  # Không cần kiểm tra tiếp
    p = g.copy()  # Tạo đồ thị trung gian chứa các node có đuôi S và chỉ nối với node có đuôi S và duôi D của chính nó

    for nodee in list(p.nodes()):
        if nodee.endswith('S'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A
            for neighbor in p.neighbors(nodee):
                if neighbor.endswith('D'):
                    if neighbor[:-1] != base_node:
                        # Nếu *E nối với *D nhưng khác gốc => xóa node *E
                        p.remove_node(nodee)
                        break  # Không cần kiểm tra tiếp
    node_connect1, node_degree1, i = lowest_degree_arr_node(f, 'D', i, inter_arr, '')           #tìm ra điểm có đuôi D và bậc nhỏ nhất
    node_connect2, node_degree2, j = lowest_degree_arr_node(p, 'S', j, inter_arr, '')
    if mode == 0:
        g.add_edge(n1, node_connect1)
        for node in g.nodes():
            if node[0] == node_connect1[0]: continue
            if (node_connect1, node) in g.edges() and node[1] == 'D':
                g.add_edge(n1, node)
    elif mode == 1:
        if check_serial_connected(g, node, inter_arr) == True:
            g.add_edge(n2, node_connect2)
            for node in g.nodes():
                if node[0] == node_connect2[0]: continue
                if (node_connect2, node) in g.edges() and node[1] == 'D':
                    g.add_edge(n2, node)
        else:     
            for neighbor in list(g.neighbors(n1)):
                if neighbor.endswith('D'):
                    if neighbor[:-1] != node:
                        for neigh in list(g.neighbors(neighbor)):      
                            if neigh.endswith('D'):      
                                g.add_edge(n1, neigh)
            for neighborr in list(g.neighbors(n2)):
                if neighborr.endswith('S'):
                    if neighborr[:-1] != node:
                        for neighh in list(g.neighbors(neighborr)):      
                            if neighh.endswith('S'):      
                                g.add_edge(n2, neighh)
                        # Nếu *E nối với *D nhưng khác gốc => xóa node *E
                            

#thêm các cạnh song song (parallel edges) giữa một node cho trước với các node khác trong đồ thị g.

def add_edge_parallel_2(g, node, inter_arr):
    n1 = node + 'S'                             #DS
    n2 = node + 'D'                             #DD
    outside_node = ''
    
    for n in g.nodes():                         #
        if n[0] not in inter_arr and n[0] != node:
            outside_node = n[0]
            break

    outside_node1 = []
    for n in g.nodes():
        if n[0] not in inter_arr and n[0] != node:
            outside_node1.append(n[0])

    p = g.copy()  # Tạo đồ thị trung gian chứa các node có đuôi S và chỉ nối với node có đuôi S và duôi D của chính nó
    for nodee in list(p.nodes()):
        if any(nodee[:-1] == outside for outside in outside_node1):
            p.remove_node(nodee)
    for nodee in list(p.nodes()):
        if nodee.endswith('S'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A
            for neighbor in p.neighbors(nodee):
                if neighbor.endswith('D'):
                    if neighbor[:-1] != base_node:
                        # Nếu *E nối với *D nhưng khác gốc => xóa node *E
                        p.remove_node(nodee)
                        break  # Không cần kiểm tra tiếp

    f = g.copy()  # Tạo đồ thị trung gian
    for nodee in list(f.nodes()):
        if any(nodee[:-1] == outside for outside in outside_node1):
            f.remove_node(nodee)

    for nodee in list(f.nodes()):
        if nodee.endswith('D'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A

            for neighbor in f.neighbors(nodee):
                if neighbor.endswith('S'):
                    if neighbor[:-1] != base_node:
                        # Nếu *E nối với *D nhưng khác gốc => xóa node *E
                        f.remove_node(nodee)
                        
                        break  # Không cần kiểm tra tiếp
    node1 = lowest_degree(p, 'S', node, node, outside_node)
    node2 = lowest_degree(f, 'D', node, node, outside_node)
    if node1 is None or node2 is None:
        print(f"[WARNING] Không tìm thấy node phù hợp trong add_edge_parallel_2 với node {node}")
        return  # dừng lại an toàn, tránh lỗi

    node1_degree = p.degree(node1)
    node2_degree = f.degree(node2)
    if node1_degree < node2_degree:
        s = 1
        g.add_edge(n1, node1)
        for node_e in p.nodes():
            if node_e[0] == node1[0]: continue
            if (node1, node_e) in g.edges() and node_e[1] == 'S'and node_e != n1 :
                g.add_edge(n1, node_e)
    else:
        s = 2
        g.add_edge(n2, node2)
        for node_e in f.nodes():
            if node_e[0] == node2[0]: continue
            if (node2, node_e) in g.edges() and node_e[1] == 'D'and node_e != n2 :
                g.add_edge(n2, node_e)
                
    if s == 1:
        node1_base = node1[0]
        node_connect = lowest_degree(g, 'D', node, node1_base, outside_node)
        if node_connect:
            g.add_edge(n2, node_connect)
            for node_e in f.nodes():
                if node_e[0] == node_connect[0]: continue
                if (node_connect, node_e) in g.edges() and node_e[1] == 'D'and node_e != n2 :
                    g.add_edge(n2, node_e)
    elif s == 2:
        node2_base = node2[0]
        node_connect = lowest_degree(p, 'S', node, node2_base, outside_node)
        if node_connect:
            g.add_edge(n1, node_connect)
            for node_e in p.nodes():
                if node_e[0] == node_connect[0]: continue
                if (node_connect, node_e) in g.edges() and node_e[1] == 'S'and node_e != n1 :
                    g.add_edge(n1, node_e)

###nối các cạnh song song giữa các node trong danh sách inter_arr.
def add_edge_parallel_3(g, inter_arr, mode):

    p = g.copy()  # Tạo đồ thị trung gian chứa các node có đuôi S và chỉ nối với node có đuôi S và duôi D của chính nó
    
    for nodee in list(p.nodes()):
        if nodee.endswith('S'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A
            for neighbor in p.neighbors(nodee):
                if neighbor.endswith('D'):
                    if neighbor[:-1] != base_node:
                        # Nếu *E nối với *D nhưng khác gốc => xóa node *E
                        p.remove_node(nodee)
                        break  # Không cần kiểm tra tiếp
    f = g.copy()  # Tạo đồ thị trung gian

    for nodee in list(f.nodes()):
        if nodee.endswith('D'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A

            for neighbor in f.neighbors(nodee):
                if neighbor.endswith('S'):
                    if neighbor[:-1] != base_node:
                        # Nếu *E nối với *D nhưng khác gốc => xóa node *E
                        f.remove_node(nodee)
                        
                        break  # Không cần kiểm tra tiếp
    i = 0
    j = 0
    n1 = n2 = n3 = n4 = ''
    n1_degree = n2_degree = n3_degree = n4_degree = 0
    n1, n1_degree, i = lowest_degree_arr_node(p, 'S', i, inter_arr, '')     #CS        
    t1 = i
    n2, n2_degree, i = lowest_degree_arr_node(p, 'S', i, inter_arr, '')     #AS
    n3, n3_degree, j = lowest_degree_arr_node(f, 'D', j, inter_arr, '')     #DD bậc 1
    n4, n4_degree, j = lowest_degree_arr_node(f, 'D', j, inter_arr, '')     #AD                                                  
    sel = 3

    if n1 is None or n2 is None or n3 is None or n4 is None:
        print(f"[WARNING] Không tìm thấy node phù hợp trong add_edge_parallel_2 với node {node}")
        return  # dừng lại an toàn, tránh lỗi

    if n1_degree + n2_degree < n3_degree + n4_degree :
        if checking_parallel_connected(g, 'S', inter_arr) == True and mode == 1:
            sel = 0
            g.add_edge(n1, n2)      #S->S
            for node_e in p.nodes():
                if node_e[0] == n1[0]: continue
                if (n1, node_e) in g.edges() and node_e[1] == 'S'and node_e != n2 :
                    g.add_edge(n2, node_e)
            for node_e in p.nodes():
                if node_e[0] == n2[0]: continue
                if (n2, node_e) in g.edges() and node_e[1] == 'S'and node_e != n1 :
                    g.add_edge(n1, node_e)
        elif mode == 0:
            sel = 0
            g.add_edge(n1, n2)      #S->S
            for node_e in p.nodes():
                if node_e[0] == n1[0]: continue
                if (n1, node_e) in g.edges() and node_e[1] == 'S'and node_e != n2 :
                    g.add_edge(n2, node_e)
            for node_e in p.nodes():
                if node_e[0] == n2[0]: continue
                if (n2, node_e) in g.edges() and node_e[1] == 'S'and node_e != n1 :
                    g.add_edge(n1, node_e)
    else:
        if checking_parallel_connected(g, 'D', inter_arr) == True and mode == 1:
            sel = 1
            g.add_edge(n3, n4)      #D->D
            for node_e in f.nodes():
                if node_e[0] == n3[0]: continue
                if (n3, node_e) in g.edges() and node_e[1] == 'D'and node_e != n4 :
                    g.add_edge(n4, node_e)
            for node_e in f.nodes():
                if node_e[0] == n4[0]: continue
                if (n4, node_e) in g.edges() and node_e[1] == 'D'and node_e != n3 :
                    g.add_edge(n3, node_e)
        elif mode == 0:
            sel = 1
            g.add_edge(n3, n4)      #D->D
            for node_e in f.nodes():
                if node_e[0] == n3[0]: continue
                if (n3, node_e) in g.edges() and node_e[1] == 'D'and node_e != n4 :
                    g.add_edge(n4, node_e)
            for node_e in f.nodes():
                if node_e[0] == n4[0]: continue
                if (n4, node_e) in g.edges() and node_e[1] == 'D'and node_e != n3 :
                    g.add_edge(n3, node_e)
    if sel == 1 :   #connect S -> S
        except_node = n4[0]
        node_connect, node_degree, t1 = lowest_degree_arr_node(p, 'S', t1, inter_arr, except_node)
        g.add_edge(n1, node_connect)
        for node_e in p.nodes():
            if node_e[0] == node_connect[0]: continue
            if (node_connect, node_e) in g.edges() and node_e[1] == 'S'and node_e != n1 :
                g.add_edge(n1, node_e)
        for node_e in p.nodes():
                if node_e[0] == n1[0]: continue
                if (n1, node_e) in g.edges() and node_e[1] == 'S'and node_e != node_connect :
                    g.add_edge(node_connect, node_e)
    elif sel == 2:           #connect d->D
        except_node = n2[0]
        node_connect, node_degree, t1 = lowest_degree_arr_node(f, 'D', t1, inter_arr, except_node)
        g.add_edge(n3, node_connect)
        for node_e in f.nodes():
            if node_e[0] == node_connect[0]: continue
            if (node_connect, node_e) in g.edges() and node_e[1] == 'D'and node_e != n3 :
                g.add_edge(n3, node_e)
        for node_e in f.nodes():
                if node_e[0] == n3[0]: continue
                if (n3, node_e) in g.edges() and node_e[1] == 'D'and node_e != node_connect :
                    g.add_edge(node_connect, node_e)
    return

#nối tiếp hai transistor trong đồ thị mạch g.
def add_edge_serial_3(g, inter_arr, mode):
    i = 0

    f = g.copy()  # Tạo đồ thị trung gian
    for nodee in list(f.nodes()):
        if nodee.endswith('D'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A

            for neighbor in f.neighbors(nodee):
                if neighbor.endswith('S'):
                    if neighbor[:-1] != base_node:
                        # Nếu *S nối với *D nhưng khác gốc => xóa node *D
                        f.remove_node(nodee)
                        break  # Không cần kiểm tra tiếp
    p = g.copy()  # Tạo đồ thị trung gian chứa các node có đuôi S và chỉ nối với node có đuôi S và duôi D của chính nó

    for nodee in list(p.nodes()):
        if nodee.endswith('S'):
            base_node = nodee[:-1]  # Lấy phần gốc, ví dụ AE -> A
            for neighbor in p.neighbors(nodee):
                if neighbor.endswith('D'):
                    if neighbor[:-1] != base_node:
                        # Nếu *E nối với *D nhưng khác gốc => xóa node *E
                        p.remove_node(nodee)
                        break  # Không cần kiểm tra tiếp
    n1, n1_degree, i = lowest_degree_arr_node(p, 'S', i, inter_arr, '')
    n2 , n2_degree, i = lowest_degree_arr_node(f, 'D', i, inter_arr, n1)
    if mode == 0:
        g.add_edge(n1, n2)
        for node in g.nodes():
            if (node, n1) in g.edges() and node[1] == 'S':
                g.add_edge(node, n2)
            if (node, n2) in g.edges() and node[1] == 'D':
                g.add_edge(node, n1)
    elif mode == 1:
        if check_serial_connected(g, '', inter_arr) == True:
            g.add_edge(n1, n2) 
            for node in g.nodes():
                if (node, n1) in g.edges() and node[1] == 'S':
                    g.add_edge(node, n2)
                if (node, n2) in g.edges() and node[1] == 'D':
                    g.add_edge(node, n1)
#tìm kiếm nút có bậc thấp nhất trong một mảng các node được cho trước.
def lowest_degree_arr_node(g, k, i, inter_arr, except_node):
    t = i
    min_degree1 = 100
    min_node1 = None
    min_degree2 = 100
    while 1:
        if inter_arr[t] == 0:
            t += 1
            break
        n1 = inter_arr[t] + k

        if n1 not in g:
            t += 1
            continue  # Bỏ qua nếu node không tồn tại trong đồ thị

        n1_degree = g.degree(n1)

        if (n1_degree < min_degree1) and (n1 != except_node):
            min_node1 = n1
            min_degree1 = n1_degree
        t += 1
    return min_node1, min_degree1, t

#tìm node có bậc thấp nhất trong đồ thị g.
# def lowest_degree(g, k, except_node1, except_node2, except_node3):
#     degrees = dict(g.degree())                      #lấy bậc của tất cả các node trong đồ thị g và lưu vào một dictionary degrees.
#     if except_node1 != '':
#         degrees.pop(except_node1 + 'S', None)       #giúp loại bỏ một phần tử trong dictionary nếu nó tồn tại.
#         degrees.pop(except_node1 + 'D', None)
#     if except_node2 != '':
#         degrees.pop(except_node2 + 'S', None)
#         degrees.pop(except_node2 + 'D', None)
#     if except_node3 != '':
#         degrees.pop(except_node3 + 'S', None)
#         degrees.pop(except_node3 + 'D', None)
#     #filtered_degrees = {node: degree for node, degree in degrees.items() if node[-1] == k}  #Lọc ra những node mà tên của chúng có ký tự cuối là k.
#     #lowest_degree_node = min(filtered_degrees, key=degrees.get)                             #Tìm node có bậc thấp nhất.
#     filtered_degrees = {node: degree for node, degree in degrees.items() if node[-1] == k}

#     if not filtered_degrees:
#         return None  # hoặc trả về giá trị mặc định như '', 1000, 0 tùy bạn xử lý sau

#     lowest_degree_node = min(filtered_degrees, key=degrees.get)
#     return lowest_degree_node

def lowest_degree(g, k, except_node1, except_node2, except_node3):
    degrees = dict(g.degree())
    if except_node1 != '':
        degrees.pop(except_node1 + 'S', None)
        degrees.pop(except_node1 + 'D', None)
    if except_node2 != '':
        degrees.pop(except_node2 + 'S', None)
        degrees.pop(except_node2 + 'D', None)
    if except_node3 != '':
        degrees.pop(except_node3 + 'S', None)
        degrees.pop(except_node3 + 'D', None)
    filtered_degrees = {node: degree for node, degree in degrees.items() if node[-1] == k}
    if not filtered_degrees:  # Kiểm tra nếu filtered_degrees rỗng
        return None  # hoặc ném ngoại lệ, ví dụ: ValueError("Không tìm thấy node có hậu tố k")
    lowest_degree_node = min(filtered_degrees, key=degrees.get)
    return lowest_degree_node



#xây dựng đồ thị biểu diễn biểu thức logic từ một chuỗi ký tự toán tử + toán hạng
def create_graph(g, q, i, expression, mode):
    end_node = ''
    inter_arr = []
    t = i - 1
    expre = expression
    while t >= 0:
        element = q[t]
        inter = intersection_expressions(expre, element)
        if len(inter) > 0:
            for char in inter:
                if char.isalpha():
                    inter_arr.append(char)
            inter_arr.append(0)
        remain = subtract_expressions(expre, element)
        if len(remain) > 0:
            expre = remain
        t -= 1
    if expre == expression:
        sel = 0
        for token in expression:
            if token.isalpha():
                create_node(g, token)
                if sel == 0:
                   sel = 1
                   node1 = token
                else:
                    node2 = token
                   
            elif token in '+*':
                operator = precedence(token)
                
        if operator == 1:
            add_edge_parallel_1(g, node1, node2)
        else:
            add_edge_serial_1(g, node1, node2, inter_arr, mode)

    else:
        node = ''
        for token in expre:
            
            if token in '+*':
                operator = precedence(token)
            elif token.isalpha():
                node = token
                create_node(g, token)
        if operator == 1:
            if len(node) > 0:
                add_edge_parallel_2(g, node, inter_arr)
            else:
                add_edge_parallel_3(g, inter_arr, mode)
        else:
            if len(node):
                add_edge_serial_2(g, node, inter_arr, mode)
            else:
                add_edge_serial_3(g, inter_arr, mode)
        end_node = node
    return g, end_node

#xây dụng nmos.
def create_nmos(g, expression):
    q = []
    end_node = ''
    evaluate_expression(expression, q)
    i = 0
    while i < len(q):
        g, end_node = create_graph(g, q, i, q[i], 0)
        i += 1
    return g, end_node

#xây dựng pmos.
def create_pmos(g, expression, euler_path):
    q = []
    evaluate_expression_inv(expression, q)
    i = 0
    while i < len(euler_path):
        n1 = euler_path[i]
        g.add_node(n1)
        if i != 0:
            n2 = euler_path[i - 1]
            g.add_edge(n1, n2)
        i += 1
    i = 0
    while i < len(q):
        create_graph(g, q, i, q[i], 1)
        i += 1
    return g

def merge_duplicate_nodes(graph, var_mapping):
    merged_graph = nx.Graph()
    name_map = defaultdict(list)
    
    for node in graph.nodes:
        original_var = var_mapping.get(node[0], node[0])
        name_map[(original_var, node[1])].append(node)

    for (base, pin), nodes in name_map.items():
        new_name = base + pin
        merged_graph.add_node(new_name)
        for node in nodes:
            for neighbor in graph.neighbors(node):
                neighbor_original = var_mapping.get(neighbor[0], neighbor[0])
                merged_neighbor = neighbor_original + neighbor[1]
                merged_graph.add_node(merged_neighbor)
                merged_graph.add_edge(new_name, merged_neighbor)

    return merged_graph


#kiểm tra xem một đỉnh v có hợp lệ để thêm tiếp vào đường đi path trong đồ thị G không
def is_valid_next_node(v, path, G):
    # Kiểm tra xem đỉnh v đã được thêm vào path chưa
    if v in path:
        return False
    #Kiểm tra các node S D có nằm cạnh nhau không
    last_node = path[-1]
    if last_node[0] != v[0] :
        if last_node[1] == 'S':
            x = last_node[0] + 'D'
            if x in path:
                return True
            else: return False
        if last_node[1] == 'D':
            x = last_node[0] + 'S'
            if x in path:
                return True
            else: return False

    # Kiểm tra xem đỉnh v có kề với đỉnh cuối cùng của path không
    if not path or v in G.neighbors(path[-1]):
        return True
    return False

#tìm đường đi Hamilton trong đồ thị có hướng G
def hamiltonian_dfs_endnode(G, start, end, path=[]):
    path = path + [start]
    if len(path) == len(G.nodes()):
        return path
    for v in G.neighbors(start):
        if is_valid_next_node(v, path, G):
            new_path = hamiltonian_dfs_endnode(G, v, end, path)
            if new_path:
                return new_path
    return None

#tìm đường đi Hamilton trong đồ thị có hướng G
def hamiltonian_dfs(G, start, path=[]):
    path = path + [start]
    if len(path) == len(G.nodes()):
        return path
    for v in G.neighbors(start):
        if is_valid_next_node(v, path, G):
            new_path = hamiltonian_dfs(G, v, path)
            if new_path:
                return new_path
    return None

#tìm một đường đi Hamilton hợp lệ trên đồ thị g, có thể với hoặc không với ràng buộc điểm kết thúc là end_node.
def find_hamilton_path(g, end_node):
    path = []
    for node in g.nodes():
        if node[1] == 'S': continue
        if end_node != '':
            path = hamiltonian_dfs_endnode(g, node, end_node)
            if path:
                if (path[0][0] != end_node and path[-1][0] != end_node):
                    path = []
        else:  path = hamiltonian_dfs(g, node)
        if path :
            break
        path = []
    if path:
        return path
    else: 
        for node in g.nodes():
            if node[1] == 'D': continue
            if end_node != '':
                path = hamiltonian_dfs_endnode(g, node, end_node)
                if path:
                    if (path[0][0] != end_node and path[-1][0] != end_node):
                        path = []
            else:  path = hamiltonian_dfs(g, node)
            if path :
                break
            path = []
    return path

#tạo ra hai đường đi song song từ một đường đi Hamilton
def euler_path(g, end_node):
    euler_path_nmos = find_hamilton_path(g, end_node)
    if not euler_path_nmos:
        return None
    euler_path_pmos = [None] * len(euler_path_nmos)
    i = 0
    s = False
    while i < len(euler_path_nmos) - 1:
        if s == True:
            euler_path_pmos[i] = euler_path_nmos[i+1]
            euler_path_pmos[i+1] = euler_path_nmos[i]
        else:
            euler_path_pmos[i] = euler_path_nmos[i]
            euler_path_pmos[i+1] = euler_path_nmos[i+1]
        s = not s
        i += 2
    return euler_path_nmos, euler_path_pmos

#lọc (hoặc chỉnh sửa) các cạnh PMOS trong đồ thị g.
def filter_edge_pmos(g, arr1, arr2, euler_path):
    # Khởi tạo danh sách kiểm tra các cặp node nối tiếp và song song
    check_serial = []
    check_parallel = []
    
    # Xây dựng check_serial và check_parallel từ euler_path
    for i in range(1, len(euler_path)):
        n1 = euler_path[i]
        n2 = euler_path[i - 1]
        if n1[0] != n2[0] and n1[1] != n2[1]:
            check_serial.append(n1[0] + n2[0])
            check_serial.append(n2[0] + n1[0])
        if n1[0] != n2[0] and n1[1] == n2[1]:
            check_parallel.append(n1[0] + n2[0] + n1[1])
            check_parallel.append(n2[0] + n1[0] + n1[1])
    # Hàm kiểm tra tính liên thông của đồ thị theo đường Euler
    def is_euler_path_valid(g, euler_path):
        for i in range(1, len(euler_path)):
            n1 = euler_path[i]
            n2 = euler_path[i - 1]
            if n1[0] != n2[0] and n1[1] != n2[1]:  # Chỉ kiểm tra các cạnh nối tiếp
                if (n1, n2) not in g.edges() and (n2, n1) not in g.edges():
                    return False
        return True

    # Sao chép danh sách cạnh để tránh lỗi khi chỉnh sửa đồ thị
    edges_to_remove = []
    for edge in g.edges():
        n1 = edge[0][0]  # Đầu của node đầu tiên (e.g., 'B' từ 'BS')
        n2 = edge[1][0]  # Đầu của node thứ hai (e.g., 'A' từ 'AD')
        if n1 == n2:  # Bỏ qua các cạnh nội tại (e.g., BS--BD)
            continue
        n3 = edge[0][1]  # Đuôi của node đầu tiên (e.g., 'S')
        n4 = edge[1][1]  # Đuôi của node thứ hai (e.g., 'D')
        
        node1 = n1 + n2  # e.g., 'BA'
        node2 = n2 + n1  # e.g., 'AB'
        
        # Trường hợp cạnh khác đuôi (có thể là nối tiếp trong PMOS)
        if n3 != n4:
            if (node1 in arr1 or node2 in arr1) and (node1 not in check_serial and node2 not in check_serial):
                edges_to_remove.append(edge)
        
        # Trường hợp cạnh cùng đuôi (song song trong PMOS)
        else:
            if node1 not in arr2 and node2 not in arr2:
                for n in check_parallel:
                    if node1 != n[0] + n[1] and node2 != n[0] + n[1] and n3 == n[2]:
                        if (n1 + n[2], n2 + n[2]) in g.edges():
                            edges_to_remove.append((n1 + n[2], n2 + n[2]))

    # Xóa các cạnh không cần thiết và kiểm tra thay thế
    for edge in edges_to_remove:
        if edge in g.edges():
            # Tạo bản sao đồ thị để kiểm tra
            g_temp = g.copy()
            g_temp.remove_edge(*edge)
            
            # Kiểm tra xem đường Euler có còn hợp lệ không
            if not is_euler_path_valid(g_temp, euler_path):
                n1, n2 = edge[0][0], edge[1][0]
                n3, n4 = edge[0][1], edge[1][1]
                s = 0
                if (n1 + 'S', n2 + 'D') == edge:
                    s = 1
                elif (n1 + 'D', n2 + 'S') == edge:
                    s = 2
                
                # Chỉ thêm cạnh thay thế nếu cần thiết và phù hợp với check_serial
                if s == 1:
                    for node in g.nodes():
                        if (node, n2 + 'D') in g.edges() and node[1] == 'S':
                            new_edge = (n1 + 'S', node[0] + 'D')
                            new_node1 = n1 + node[0]
                            new_node2 = node[0] + n1
                            if new_node1 in check_serial or new_node2 in check_serial:
                                g_temp.add_edge(*new_edge)
                            break
                elif s == 2:
                    for node in g.nodes():
                        if (node, n2 + 'S') in g.edges() and node[1] == 'D':
                            new_edge = (n1 + 'D', node[0] + 'S')
                            new_node1 = n1 + node[0]
                            new_node2 = node[0] + n1
                            if new_node1 in check_serial or new_node2 in check_serial:
                                g_temp.add_edge(*new_edge)
                            break
            
            # Cập nhật đồ thị chính
            g.remove_edge(*edge)
            if g_temp != g:
                for new_edge in g_temp.edges():
                    if new_edge not in g.edges():
                        g.add_edge(*new_edge)

    return g

#kiểm tra tính hợp lệ của các cạnh trong đồ thị g.
def checking_edge(g, full_node, char_connected):
    for node in g.nodes():
        if node[0] == full_node[0] : continue
        if char_connected == '':
            if(full_node, node) in g.edges():
                return False
        else:
            if node[1] == char_connected:
                if(full_node, node) in g.edges():
                    return False
    return True

#tìm các đỉnh nguồn (source_nodes) và đỉnh ra (out_nodes) trong đồ thị g dựa trên các điều kiện kết nối giữa các đỉnh của đồ thị.
def find_node_source_and_out(g):
    source_nodes = []
    out_nodes = []
    for edge in g.edges():
        if edge[0][0] == edge[1][0]: continue
        if edge[0][1] == edge[1][1]:
            if edge[0][1] == 'S':
                source_nodes.append((edge[0][0], edge[1][0]))
            else:
                out_nodes.append((edge[0][0], edge[1][0]))
    if len(source_nodes) > 0:
        temp1 = []
        for pair in source_nodes:
            temp1.append(pair)
        for pair in temp1:
            n1 = pair[0]
            n2 = pair[1]
            n1_s = n1 + 'S'
            n2_s = n2 + 'S'
            if checking_edge(g, n1_s, 'D') == False or checking_edge(g, n2_s, 'D') == False:
                source_nodes.remove((n1, n2))
        if len(source_nodes) > 0:
            temp1 = []
            i = 0
            j = len(source_nodes)
            while i < j:
                n1 = source_nodes[0][0]
                n2 = source_nodes[0][1]
                n1_s = n1 + 'S'
                n2_s = n2 + 'S'
                source_nodes.remove((n1, n2))
                temp1.append(n1_s)
                temp1.append(n2_s)
                i += 1
            source_nodes = temp1
    if len(out_nodes) > 0:
        temp2 = []
        for pair in out_nodes:
            temp2.append(pair)
        for pair in temp2:

            n1 = pair[0]
            n2 = pair[1]
            n1_d = n1 + 'D'
            n2_d = n2 + 'D'
            if checking_edge(g, n1_d, 'S') == False or checking_edge(g, n2_d, 'S') == False:
                out_nodes.remove((n1, n2))
        if len(out_nodes) > 0:
            temp2 = []
            i = 0
            j = len(out_nodes)
            while i < j:
                n1 = out_nodes[0][0]
                n2 = out_nodes[0][1]
                n1_s = n1 + 'D'
                n2_s = n2 + 'D'
                out_nodes.remove((n1, n2))
                temp2.append(n1_s)
                temp2.append(n2_s)
                i += 1
            out_nodes = temp2
    
    temp1 = []
    for node in source_nodes:
        temp1.append(node)

    for node in temp1:
        if checking_edge(g, node, '') == False:
            if node in source_nodes:
                source_nodes.remove(node)
    if len(source_nodes) == 0:            
        for node in g.nodes():
            if node[1] == 'S':
                if checking_edge(g, node, '') == True:
                    source_nodes.append(node)
    if len(source_nodes) == 0: source_nodes = temp1

    temp2 = []
    for node in out_nodes:
        temp2.append(node)
    for node in temp2:
        if checking_edge(g, node, '') == False:
            if node in out_nodes:
                out_nodes.remove(node)
    if len(out_nodes) == 0:
        for node in g.nodes():
            if node[1] == 'D':
                if checking_edge(g, node, '') == True:
                    out_nodes.append(node)
    if len(out_nodes) == 0: out_nodes = temp2
                
    return source_nodes, out_nodes

'''def find_node_source_and_out(g):
    source_nodes = []
    out_nodes = []
    for node in g.nodes():
        if node[1] == 'S':
            if checking_edge(g, node, 'D') == True:
                source_nodes.append(node)
        else:
            if checking_edge(g, node, 'S') == True:
                out_nodes.append(node)
    return source_nodes, out_nodes'''

#xây dựng đồ thị cho mạch NMOS và PMOS từ một biểu thức số học cho trước.
def Create_All(expression):
    expression_str = expression
    expression,rename_map = simplify_expression(expression)
    expression_renamed, var_mapping = rename_duplicate_variables(expression)
    print("Biểu thức sau khi rút gọn: ", expression)
    print("Danh sách các node thay thế cho nhau: ", rename_map)
    g_nmos = nx.Graph()
    g_pmos = nx.Graph()
    node = ''

    # NMOS: tạo + merge
    g_nmos, node = create_nmos(g_nmos, expression_renamed)
    g_nmos = merge_duplicate_nodes(g_nmos, var_mapping)
    source_nodes_nmos, out_nodes_nmos = find_node_source_and_out(g_nmos)
    if not out_nodes_nmos:
        for n in g_nmos.nodes():
            if n[1] == 'D':
                out_nodes_nmos.append(n)

    # Phân tích NMOS để chuẩn bị tạo PMOS
    serial_array_pmos = []
    parallel_array_pmos = []
    for edge in g_nmos.edges():
        n1, n2 = edge[0][0], edge[1][0]
        if n1 == n2: continue
        if edge[0][1] == edge[1][1]:
            serial_array_pmos.append(n1 + n2)
        else:
            parallel_array_pmos.append(n1 + n2)
    # Tạo Euler path + PMOS
    euler_path_nmos, euler_path_pmos = euler_path(g_nmos, node)
    g_pmos = create_pmos(g_pmos, expression_renamed, euler_path_pmos)
    g_pmos = filter_edge_pmos(g_pmos, serial_array_pmos, parallel_array_pmos, euler_path_pmos)
    g_pmos = merge_duplicate_nodes(g_pmos, var_mapping)
    var_mapping = restore_var_mapping_full(var_mapping, rename_map)
    # Tìm đầu vào / đầu ra PMOS
    source_nodes_pmos, out_nodes_pmos = find_node_source_and_out(g_pmos)
    #if not out_nodes_pmos:
       #for n in g_pmos.nodes():
            #if n[1] == 'S':
               # out_nodes_pmos.append(n)

    return g_nmos, g_pmos, euler_path_nmos, euler_path_pmos, source_nodes_nmos, out_nodes_nmos, source_nodes_pmos, out_nodes_pmos, var_mapping, expression_str,rename_map

