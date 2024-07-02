from collections import defaultdict
import re
import os
import murphi
from inv2OPexpr import parse_single_inv
import murphiparser as parser
from process import to_murphi, simplify, string2tuple, merge_tuple2string
from call_murphi import multi_callmurphi


#Separate the conjunction
def seperation(expr):
    if isinstance(expr, murphi.OpExpr) and expr.op == '&':
        sep = []
        expr1, expr2 = expr.expr1, expr.expr2
        sep.append(expr1)
        return sep+seperation(expr2)
    else:
        return [expr]
    
def get_guard(file_name, rule_name):
    print("you wanna reading \"{}\", rule-{}".format(file_name, rule_name))
    file_name = './{}/{}.m'.format(file_name, file_name) 
    prot = parser.parse_file(file_name)
    for k,r in prot.rule_map.items():
        if isinstance(r,murphi.MurphiRuleSet) and str(k) == rule_name:
            decl = r.var_decls
            rule = r.rule
            cond = str(rule.cond)
            cnt = 1
            for var_decl in decl:
                cond = re.sub(str(var_decl.name), '{}_{}'.format(var_decl.typ,cnt), cond, flags=re.S)
                cnt += 1
            guard = seperation(parse_single_inv(cond))
    return guard
            
#Combine the conjuncts
def combine(expr_list):
    length = len(expr_list)
    temp_expr = expr_list[-1]
    for i in range(length-2, -1, -1):
        temp_expr = murphi.OpExpr('&', expr_list[i], temp_expr)
    return temp_expr

#Find the index og local var
def find_index(atom):
    assert isinstance(atom, murphi.OpExpr) and atom.op in ('=', '!='), 'atom is {}'.format(atom)
    if isinstance(atom.expr1, murphi.FieldName):
            temp_v = atom.expr1.v
            if isinstance(temp_v, murphi.ArrayIndex):
                return str(temp_v.idx)
    elif isinstance(atom.expr1, murphi.ArrayIndex):
        return str(atom.expr1.idx)
    return ''

# Determines whether an expression is a local variable
def is_local_var(atom):
    if isinstance(atom, list):
        for a in atom:
            if isinstance(a.expr1, murphi.FieldName):
                value = a.expr1.v
                if isinstance(value, murphi.ArrayIndex):
                    return True
            else:
                if isinstance(a.expr1, murphi.ArrayIndex):
                    return True
    else:
        if isinstance(atom.expr1, murphi.FieldName):
                value = atom.expr1.v
                if isinstance(value, murphi.ArrayIndex):
                    return True
        else:
            if isinstance(atom.expr1, murphi.ArrayIndex):
                return True
    return False

# Remove the invs whose variable in antecedent are all global
def murphi_global_simple(inv_tree_list):
    res = []
    for inv in inv_tree_list:
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        local_flag = False
        atom = seperation(inv.expr1)
        local_flag = is_local_var(atom)
        if any(str(a.expr2) in ('NODE_1', 'NODE_2') for a in atom) or local_flag:
            if inv.expr2.op == '->':
                temp_pre = inv.expr2.expr1
                temp_cond = inv.expr2.expr2
                atom = seperation(temp_pre) 
                local_flag_2 = is_local_var(atom)
                if any(str(a.expr2) in ('NODE_1', 'NODE_2') for a in atom) or local_flag_2:
                    res.append(inv)
            else:
                res.append(inv)
    return res
    
# Simplify: The node in antecedent is same as in consequent
def murphi_local_simple(inv_tree_list, needReplace):
    res = []
    for inv in inv_tree_list:
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        # local_flag = False
        atom = seperation(inv.expr1)
        # local_flag = is_local_var(atom)
        pre_idx = set(map(lambda x : find_index(x), atom)) - {''}
        for a in atom:
            if  str(a.expr2) in ('NODE_1', 'NODE_2'):
                pre_idx.add(str(a.expr2))
        if len(pre_idx) != 0:
            if inv.expr2.op == '->':
                conse_1 = inv.expr2.expr1
                conse_2 = inv.expr2.expr2
                atom = seperation(conse_1) 
                conse_idx_1 = set(map(lambda x : find_index(x), atom))
                for a in atom:
                    if  str(a.expr2) in ('NODE_1', 'NODE_2'):
                        conse_idx_1.add(str(a.expr2))
                conse_idx_2 = find_index(conse_2)
                if needReplace and 'data' in str(conse_2).lower():
                    res.append(inv)
                elif all(c not in pre_idx for c in conse_idx_1) and conse_idx_2 not in pre_idx:
                    res.append(inv)
            else:
                conse = inv.expr2
                temp_conse = seperation(conse)
                if needReplace and 'data' in str(conse).lower():
                    res.append(inv)
                elif all((find_index(c) not in pre_idx and str(c.expr2) not in pre_idx) for c in temp_conse):
                    res.append(inv)
        else:
            raise ValueError('inv is {}'.format(inv))
    return res

# Remove the negative form in the antecedent
def murphi_neg_simp(inv_tree_list):
    res = []
    for inv in inv_tree_list:
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr2, murphi.OpExpr)
        temp_pre = inv.expr1
        atom = seperation(temp_pre)
        if all(a.op == '=' for a in atom):
            if inv.expr2.op == '->':
                temp_pre = inv.expr2.expr1
                atom = seperation(temp_pre)
                if all(a.op == '=' for a in atom):
                    res.append(inv)
            else:
                res.append(inv)
    return res

# simplify：p -> a -> a / p -> (p & b) ->a / p -> a -> p
def murphi_repeat_simple(inv_tree_list):
    res = []
    for inv in inv_tree_list:
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        atom = seperation(inv.expr1)
        temp_atom = list(map(lambda x: str(x.expr1), atom))
        if inv.expr2.op == '->':
            temp_pre = inv.expr2.expr1
            temp_cond = inv.expr2.expr2
            atom_2 = str(temp_cond.expr1)
            if temp_cond not in temp_atom:
                atom = seperation(temp_pre)
                atom_1 = list(map(lambda x: str(x.expr1), atom))
                if atom_2 not in temp_atom and atom_2 not in atom_1:
                    if all(a not in temp_atom for a in atom_1):
                        temp_pre = combine(atom)
                        # res.append(murphi.OpExpr('->', inv.expr1, murphi.OpExpr('->', temp_pre, temp_cond)))
                        res.append(inv)
        else:
            temp_cond = inv.expr2
            atom_2 = str(temp_cond.expr1)
            if temp_cond not in temp_atom:
                # res.append(murphi.OpExpr('->', inv.expr1, inv.expr2))
                res.append(inv)
    return res

# Remove the negative value when there is a positive value in the consequent
def murphi_has_pos_simple(inv_tree_list):
    ans = []
    rule_dict = dict()
    for inv in inv_tree_list:
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        frozen_pre = frozenset(map(lambda x : str(x), seperation(inv.expr1)))
        if frozen_pre not in rule_dict:
            rule_dict.update({frozen_pre:dict()})
        if inv.expr2.op in ('=', '!='):
            atom, res = str(inv.expr2.expr1), str(inv.expr2.expr2)
            if atom not in rule_dict[frozen_pre]:
                rule_dict[frozen_pre].update({atom : {'pos':[], 'neg':[]}})
            if  inv.expr2.op == '=':
                rule_dict[frozen_pre][atom]['pos'].append(res)
            elif inv.expr2.op == '!=':
                rule_dict[frozen_pre][atom]['neg'].append(res)
            else:
                raise ValueError('error expression: {}'.format(inv.expr2))
        else:
            conse_1, conse_2 = inv.expr2.expr1, inv.expr2.expr2
            frozen_conse = frozenset(map(lambda x : str(x), seperation(conse_1)))
            if frozen_conse not in rule_dict[frozen_pre]:
                rule_dict[frozen_pre].update({frozen_conse:dict()})
            atom, res = str(conse_2.expr1), str(conse_2.expr2)
            if atom not in rule_dict[frozen_pre][frozen_conse]:
                rule_dict[frozen_pre][frozen_conse].update({atom : {'pos':[], 'neg':[]}})
            if  inv.expr2.expr2.op == '=':
                rule_dict[frozen_pre][frozen_conse][atom]['pos'].append(res)
            elif inv.expr2.expr2.op == '!=':
                rule_dict[frozen_pre][frozen_conse][atom]['neg'].append(res)
    for k, v in rule_dict.items():
        # print(v)
        for i, j in v.items():
#             print(j)
            if 'pos' in j or 'neg' in j:
                if len(j['pos']) != 0:
                    for r in j['pos']:
                        temp_inv = ' & '.join(k) + ' -> ' + i + ' = ' + r
                        ans.append(parse_single_inv(temp_inv))
                else:
                    for r in j['neg']:
                        temp_inv = ' & '.join(k) + ' -> ' + i + ' != ' + r
                        ans.append(parse_single_inv(temp_inv))
            else:
                for m,n in j.items():
                    if 'pos' in n or 'neg' in n:
                        if len(n['pos']) != 0:
                            for r in n['pos']:
                                temp_inv = ' & '.join(k) + ' -> ' + ' & '.join(i) + ' -> ' + m + ' = ' + r
                                ans.append(parse_single_inv(temp_inv))
                        else:
                            for r in n['neg']:
                                temp_inv = ' & '.join(k) + ' -> ' + ' & '.join(i) + ' -> ' + m + ' != ' + r
                                ans.append(parse_single_inv(temp_inv))
    return ans

# The invs have same antecedent are merged
def same_merge(inv_tree_list):
    res = []
    rule_dict = dict()
    for inv in inv_tree_list:
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        if inv.expr2.op == '->':
            temp_pre = str(murphi.OpExpr('->', inv.expr1, inv.expr2.expr1))
            temp_cond = str(inv.expr2.expr2)
            if temp_pre not in rule_dict:
                rule_dict.update({temp_pre:[]})
            rule_dict[temp_pre].append(temp_cond)
        else:
            temp_pre = str(inv.expr1)
            temp_cond = str(inv.expr2)
            if temp_pre not in rule_dict:
                rule_dict.update({temp_pre:[]})
            rule_dict[temp_pre].append(temp_cond)
    for k,v in rule_dict.items():
        v = list(map(lambda x:  parse_single_inv(x), v))
        temp_pre = parse_single_inv(k)
        temp_cond = combine(v)
        if temp_pre.op == '->':
            res.append(murphi.OpExpr('->', temp_pre.expr1, murphi.OpExpr('->', temp_pre.expr2, temp_cond)))
        else:
            res.append(murphi.OpExpr('->', temp_pre, temp_cond))
    return res

# simplify ：the variables in inv exsit in guard
def murphi_redundant_simple(inv_tree_list, file_name, rule_name):
    res = []
    guard = get_guard(file_name=file_name, rule_name=rule_name)
    # print('guard is :{}'.format(list(map(lambda x: str(x), guard))))
    for i, inv in enumerate(inv_tree_list):
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        f = False
        for g in guard:
            if isinstance(g, murphi.OpExpr):
                if not is_local_var(g):
                    temp_atom = g.expr1
                else:
                    continue
            elif isinstance(g, murphi.NegExpr):
                if not is_local_var(murphi.OpExpr('=', g.expr, g.expr)):
                    temp_atom = g.expr
                else:
                    continue
            else:
                continue
            if inv.expr2.op == '->':
                temp_pre = seperation(inv.expr2.expr1)
                temp_cond = inv.expr2.expr2
                if str(temp_cond.expr1) == str(temp_atom):
                    f = True
                    break
                if any(str(p.expr1) == str(temp_atom) for p in temp_pre):
                    f = True
                    break
            else:
                temp_cond = inv.expr2
                if str(temp_cond.expr1) == str(temp_atom):
                    f = True
                    break
        if f == False:
            res.append(inv)
    return res

def murphi_2decl_simple(inv_tree_list, file_name='', rule_name=''):
    res = []
    decl_len = 1
    if decl_len != 0:
        for inv in inv_tree_list:
            assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
            assert isinstance(inv.expr1, murphi.OpExpr)
            assert isinstance(inv.expr2, murphi.OpExpr)
            if inv.expr2.op == '->':
                continue
            else:
                res.append(inv)
    else:
        res = inv_tree_list

    return res

# invariants with the same consequent retains only one
def murphi_sameatom_simple(invtreelist):
    rule_dict = dict()
    res = []
    for i, inv in enumerate(invtreelist):
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        if inv.expr2.op == '->':
            temp_pre = str(murphi.OpExpr('->', inv.expr1, inv.expr2.expr1))
            temp_cond = list(map(lambda x: str(x), list(seperation(inv.expr2.expr2))))
            if temp_pre not in rule_dict:
                rule_dict.update({temp_pre:set()})
            rule_dict[temp_pre] = set(temp_cond)
        else:
            temp_pre = str(inv.expr1)
            temp_cond = list(map(lambda x: str(x), list(seperation(inv.expr2))))
            if temp_pre not in rule_dict:
                rule_dict.update({temp_pre:set()})
            rule_dict[temp_pre] = set(temp_cond)
    for k,v in rule_dict.items():
        for key in list(rule_dict.keys()):
            if key != k:
                if v & rule_dict[key]:
                    rule_dict[key] = rule_dict[key] - v
    for k,v in rule_dict.items():
        if v:
            if '->' not in k:
                res.append(k + ' -> ' + ' & '.join(v))
            else:
                res.append(k.split('->')[0] + ' -> ' + '(' + k.split('->')[1] + ' -> ' + ' & '.join(v) + ')')
    return res

def murphi_screen(flag, name, all_types, needReplace, log = None):
    #config
    data_dir = '.'
    protocol_name = name
    # read rules
    string_list = []
    rulefile = ''
    print("reading useful_rule-{}".format(flag))
    with open('./{}/useful_rule-{}.txt'.format(protocol_name,flag), 'r') as f:
        rulefile = f.read()
    rules = list(re.findall(r'rule_\w+:\s*(.*?)\n', rulefile))
    string_list = rules
    assert len(string_list) != 0
    print("read success!, useful_rules'len : {}".format(len(string_list)))
    inv_tree_list_1 = list(map(lambda x : parse_single_inv(x), string_list))
    inv_tree_list_2 = murphi_global_simple(inv_tree_list_1)
    inv_tree_list_3 = murphi_redundant_simple(inv_tree_list_2, file_name=name, rule_name=flag)
    inv_tree_list_4 = murphi_neg_simp(inv_tree_list_3)
    inv_tree_list_5 = murphi_local_simple(inv_tree_list_4, needReplace)
    print('len of inv_list is {}'.format(len(inv_tree_list_5)))
    string_list = list(map(lambda x: re.sub('\n', '', str(x), flags=re.S), inv_tree_list_5))
    # call murphi to filter invs
    if os.path.exists('./{0}/{0}.m'.format(protocol_name)):
        with open('./{0}/{0}.m'.format(protocol_name), 'r') as f:
            filter_file = f.read()
    else :
        print('reading filter_file failed!')
    filter_file = re.sub('NODE_NUM : 2', 'NODE_NUM : 3', filter_file)
    filter_file = re.sub(r'invariant.*?end\s*;','',filter_file, flags=re.S)
    remove_list = []
    rest_string_list = []
    remove_list = multi_callmurphi(filter_file, string_list, data_dir, protocol_name, all_types)
    if remove_list:
        conter_index = list(map(lambda x: int(x), remove_list))
        print("conter_index are : {}".format(conter_index))
        for i,r in enumerate(string_list):
            if i not in conter_index:
                rest_string_list.append(r)
    else:
        rest_string_list = string_list

    if len(rest_string_list) != 0 :
        simp_invs = simplify(string2tuple(rest_string_list))
        simp_invs = merge_tuple2string(simp_invs)
        inv_tree_list = list(map(lambda x : parse_single_inv(x), simp_invs))
        inv_tree_list_1 = murphi_has_pos_simple(inv_tree_list)
        inv_tree_list_2 = same_merge(inv_tree_list_1)
        invs = murphi_sameatom_simple(inv_tree_list_2)

        # count the length of invariants has not been merged
        conse_len = 0
        inv_statistic = list(map(lambda x : parse_single_inv(x), invs))
        for i in inv_statistic:
            conse_len += len(seperation(i.expr2))
        print('len of auxInvs is {}'.format(conse_len))
        log.inv_num += conse_len
        log.write_log(content='len of auxInvs is {}'.format(conse_len))

        if needReplace:
            invs = expecialForDataSplit(invs)

        if not os.path.exists('./{}/auxInvs/'.format(protocol_name)):
            os.mkdir('./{}/auxInvs/'.format(protocol_name))
        with open('./{}/auxInvs/auxInvs_{}.txt'.format(protocol_name,flag),'w') as f:
            for i, r in enumerate(invs):
                str_inv = re.sub('\n', '', str(r), flags=re.S)
                f.write('Lemma_{}: {}\n'.format(i,str_inv))  

    else:
        os.remove('./{0}/useful_rule-{1}.txt'.format(protocol_name,flag))
        return -1
    
    os.remove('./{0}/useful_rule-{1}.txt'.format(protocol_name,flag))
    return 0

def expecialForDataSplit(inv_string_list):
    res = []
    for inv_string in inv_string_list:
        inv = parse_single_inv(inv_string)
        assert isinstance(inv, murphi.OpExpr) and inv.op == '->'
        assert isinstance(inv.expr1, murphi.OpExpr)
        assert isinstance(inv.expr2, murphi.OpExpr)
        conds = inv.expr2
        cond_list = seperation(conds)
        noData = []
        data = []
        for cond_expr in cond_list:
            if isinstance(cond_expr, murphi.OpExpr) and isinstance(cond_expr.expr1, murphi.FieldName) and 'DATA' in str(cond_expr.expr1.field).upper():
                data.append(cond_expr)
            else:
                noData.append(cond_expr)
        if len(data) > 0:
            res.append(str(murphi.OpExpr('->', inv.expr1, combine(data))))
        
        res.append(str(murphi.OpExpr('->', inv.expr1, combine(noData))))

    return res
        

def construct_atoms(protocol_name):
    filename = './{0}/{0}.m'.format(protocol_name)
    output_file = './{}/atom_2.txt'.format(protocol_name)
    print("***This is a program to construct the atoms file from \"{}\"".format(filename)) 
    prot = parser.parse_file(filename)
    atom_list = list()
    para_dict = dict()
    node_num = dict()
    consts = dict()
    var_mark = defaultdict(list)
    for c in prot.consts:
        consts[c.name] = c.val
    for n, t in prot.typ_map.items():
        if str(n).lower() == 'node':
            name = str(n)
            if isinstance(t, murphi.ScalarSetType):
                node_num.update({name : int(consts[str(t.const_name)])})
            elif isinstance(t, murphi.RngType):
                node_num.update({name : int(t.upRng) - int(t.downRng) + 1})

    def get_var(e):
        if isinstance(e, murphi.ArrayIndex):
            if isinstance(e.v, murphi.FieldName):
                return get_var(e.v.v)
            return e.v
        elif isinstance(e, murphi.FieldName):
            return get_var(e.v)
        elif isinstance(e, murphi.VarExpr):
            return e

    def expand_idx(expr):
        if isinstance(expr, murphi.ArrayIndex) and str(expr.idx) in para_dict:
            typ = para_dict[str(expr.idx)]
            if str(typ).lower() == 'node':
                num = node_num[typ]
                return [murphi.ArrayIndex(expr.v, f'{typ}_{i}') for i in range(1, num+1)]
            else:
                return []
        elif isinstance(expr, murphi.FieldName):
            v = expr.v
            field = expr.field
            if isinstance(v, murphi.ArrayIndex) and str(v.idx) in para_dict:
                typ = para_dict[str(v.idx)]
                if str(typ).lower() == 'node':
                    num = node_num[typ]
                    return [murphi.FieldName(murphi.ArrayIndex(v.v, f'{typ}_{i}'), field) for i in range(1, num+1)]
                else:
                    return None
            else:
                return [expr]
        elif str(expr) in para_dict:
            typ = para_dict[str(expr)]
            if str(typ).lower() == 'node':
                num = node_num[typ]
                return [f'{typ}_{i}' for i in range(1, num+1)]
            else:
                return []
        else:
            return [expr]

    #Determine that the two variables are identical except for the index
    def same_var(var1, var2):
        temp_v1 = re.sub(r'\[\w+\]', '', var1)
        temp_v2 = re.sub(r'\[\w+\]', '', var2)
        return temp_v2 == temp_v1

    def get_atom_from_cond(e):
        if isinstance(e, murphi.OpExpr):
            if e.op == '=':
                return [e]
            elif e.op in {'|', '&', '->'}:
                return get_atom_from_cond(e.expr1) + get_atom_from_cond(e.expr2)
            else:
                return []
        elif isinstance(e, murphi.ArrayIndex) or isinstance(e, murphi.FieldName) or isinstance(e, murphi.UnknownExpr):
            return [murphi.OpExpr(op='=', expr1=e, expr2=murphi.BooleanExpr(True))]
        elif isinstance(e, murphi.NegExpr):
            if not isinstance(e.expr, murphi.OpExpr):
                return [murphi.OpExpr(op='=', expr1=e.expr, expr2=murphi.BooleanExpr(False))]
            else:
                return []
        elif isinstance(e, murphi.ForallExpr):
            nonlocal para_dict
            para_dict.update({str(e.var) : str(e.typ)})
            return get_atom_from_cond(e.expr) 
        else:
            raise ValueError('e is {}, type is {}'.format(e, type(e)))

    def get_atom_from_cmd(c):
        if isinstance(c, murphi.AssignCmd):
            # print(c, get_var(c.expr))
            # if isinstance(c.var, murphi.VarExpr) or  isinstance(c.expr, murphi.BooleanExpr) or isinstance(c.expr, murphi.VarExpr) or isinstance(c.expr, murphi.EnumValExpr):
            if str(get_var(c.expr)) in list(prot.var_map.keys()):
                for v in var_mark.keys():
                    # print(v, str(c.var), same_var(str(v), str(c.var)))
                    if same_var(str(v), str(c.var)) and var_mark[v]:
                        return [murphi.OpExpr('=', c.expr, e) for e in var_mark[v]]
                return []
            else:
                return []
        elif isinstance(c, murphi.ForallCmd):
            nonlocal para_dict
            para_dict.update({str(c.var) : str(c.typ)})
            tmp = []
            for cmd in c.cmds:
                tmp+= get_atom_from_cmd(cmd)
            return tmp
        elif isinstance(c, murphi.IfCmd):
            tmp = []
            for i in c.if_branches:
                tmp += get_atom_from_cond(i[0])
                for j in i[1]:
                    tmp += get_atom_from_cmd(j)
            if c.else_branch:
                for j in c.else_branch:
                    tmp += get_atom_from_cmd(j)
            return tmp
        elif isinstance(c, murphi.UndefineCmd):
            return []
        else:
            raise ValueError('c is {}, type is {}'.format(c, type(c)))

    #Get A_0 from rules and invariants
    for k,r in prot.rule_map.items():
        if isinstance(r, murphi.MurphiRule):
            cond = r.cond
        
        elif isinstance(r, murphi.MurphiRuleSet):
            cond = r.rule.cond
            for n, v in r.var_map.items():
                para_dict.update({str(n) : str(v)})
        
        temp_atoms = get_atom_from_cond(cond)
        for t in temp_atoms:
            assert isinstance(t, murphi.OpExpr) and t.op == '=', 'atom is {}, type is {}'.format(t, type(t))
            if str(murphi.OpExpr('=', t.expr2, t.expr1)) not in atom_list:
                atom_list.append(t)
                if str(get_var(t.expr1)) in list(prot.var_map.keys()):
                    # var_mark.add(str(get_var(t.expr1)))
                    var_mark[str(t.expr1)].append(t.expr2)
                # if str(get_var(t.expr2)) in list(prot.var_map.keys()):
                #     var_mark.add(str(get_var(t.expr2)))

    for k,inv in prot.ori_inv_map.items():
        temp_atoms = get_atom_from_cond(inv.inv)
        for t in temp_atoms:
            assert isinstance(t, murphi.OpExpr) and t.op == '=', 'atom is {}, type is '.format(t, type(t))
            if str(murphi.OpExpr('=', t.expr2, t.expr1)) not in atom_list:
                atom_list.append(t)
                if str(get_var(t.expr1)) in list(prot.var_map.keys()):
                    # var_mark.add(str(get_var(t.expr1)))
                    var_mark[str(t.expr1)].append(t.expr2)
                # if str(get_var(t.expr2)) in list(prot.var_map.keys()):
                #     var_mark.add(str(get_var(t.expr2)))
    print(var_mark)
    #Replace value of variable from action part of rules
    for k,r in prot.rule_map.items():
        if isinstance(r, murphi.MurphiRule):
            cmds = r.cmds
        
        elif isinstance(r, murphi.MurphiRuleSet):
            cmds = r.rule.cmds
        
        temp_atoms = []
        for cmd in cmds:
            temp_atoms += get_atom_from_cmd(cmd)
        for t in temp_atoms:
            assert isinstance(t, murphi.OpExpr) and t.op == '=', 'atom is {}, type is '.format(t, type(t))
            if (str(murphi.OpExpr('=', t.expr2, t.expr1)) not in atom_list):
                # if str(get_var(t.expr1)) in var_mark or str(get_var(t.expr2)) in var_mark:
                atom_list.append(t)

    #Replace i, j with NODE_1, NODE_2
    expand_list = []
    for atom in atom_list:
        assert isinstance(atom, murphi.OpExpr) and atom.op == '=', 'atom is {}, type is {}'.format(atom, type(atom))
        expand_expr1 = []
        expand_expr2 = []
        expand_expr1 += expand_idx(atom.expr1)
        expand_expr2 += expand_idx(atom.expr2)    

        for e1 in expand_expr1:
            for e2 in expand_expr2:
                expand_list.append(str(e1) + ' = ' + str(e2))
    
    expand_list = list(set(expand_list[:]))
    expand_list.sort(key=len)

    with open(output_file, 'w') as f:
        for atom in expand_list:
            f.write(atom+'\n')
            
if __name__ == "__main__":
    # flaglist = ['Store', 'NI_Remote_Get_Put', 'PI_Remote_PutX',  'NI_Local_GetX_PutX3', 'NI_Remote_Get_Put_Home', 'NI_Remote_GetX_Nak', 'NI_Remote_GetX_PutX_Home', 'NI_Remote_GetX_PutX', 'PI_Remote_PutX']
    # flaglist = ['NI_Remote_Get_Put', 'NI_Remote_GetX_PutX', 'PI_Remote_PutX',  'NI_Remote_Get_Nak', 'NI_Remote_Get_Put_Home', 'NI_Remote_GetX_Nak', 'NI_Remote_GetX_PutX_Home', 'NI_Remote_GetX_PutX', 'PI_Remote_PutX']
    # flaglist = ['NI_Remote_Get_Put']
    # # start_time = time.time()
    # for flag in flaglist:
    #     data_dir = '.'
    #     protocol_name = 'flash_data'
    #     murphi_screen(flag, name = protocol_name)
    # end_time = time.time()
    # print('The time of filter is {}'.format(str(end_time - start_time)))
    # protocol_name = 'flash_data'
    # construct_atoms(protocol_name) 

    with open('./tempInvs', 'r') as f:
        invs = f.read()
        rules = list(re.findall(r'(.*?)\n', invs))
        inv_tree_list = list(map(lambda x : parse_single_inv(x), rules))
        inv_tree_list_1 = murphi_has_pos_simple(inv_tree_list)
        print(len(inv_tree_list_1))
        inv_tree_list_2 = same_merge(inv_tree_list_1)
        print(len(inv_tree_list_2))
        invs = murphi_sameatom_simple(inv_tree_list_2)
        print(len(invs))

        # count the length of invariants has not been merged
        conse_len = 0
        invs = expecialForDataSplit(invs)

        print(invs)