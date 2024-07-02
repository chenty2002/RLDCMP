import re
from collections import defaultdict
from inv2OPexpr import parse_single_inv
import murphi
import inv2OPexpr

#Separate the conjunction
def seperation(expr):
    if isinstance(expr, murphi.OpExpr) and expr.op == '&':
        sep = []
        expr1, expr2 = expr.expr1, expr.expr2
        sep.append(expr1)
        return sep+seperation(expr2)
    else:
        return [expr]
    
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

def string2tuple(rule_string_list):
    rule_tuple = []
    for i in rule_string_list:
        preTemp, condTemp = i.split(' -> ')[0].strip(), ' -> '.join(i.split(' -> ')[1:])
        pre = set(preTemp.replace(' ', '').split('&'))
        if ' -> ' in condTemp:
            condTemp = re.findall(r'\((.*?)\)', condTemp)[0]
            conse_1, conse_2 = condTemp.split(' -> ')[0], condTemp.split(' -> ')[1]
            rule_tuple.append((pre, (set(conse_1.split(' & ')), conse_2)))
        else:
            rule_tuple.append((pre, condTemp))
    return rule_tuple

def simplify(rule_tuple):
    rule_dict = defaultdict(list)
    ans = []
    #去除p->r, p->r的情况
    for pre, conse in rule_tuple:
        froze_pre = frozenset(pre)
        if conse not in rule_dict[froze_pre]:
            rule_dict[froze_pre].append(conse)
    #去除p->r,p&q->r
    for i in list(rule_dict.keys()):
        for j in list(rule_dict.keys()):
            if i != j and i.issubset(j):
                for v in rule_dict[i]:
                    if v in rule_dict[j]:
                        rule_dict[j].remove(v)

    temp_list = []
    for k,v in rule_dict.items():
        for v1 in v:
            if isinstance(v1, str):
                ans.append((k, v1))
                temp_list.append(v1)
        for v1 in v:
            if not isinstance(v1, str):
                conse_1, conse_2 = v1
                if conse_2 not in temp_list:
                    ans.append((k,v1))
    return ans

def merge_tuple2string(inv_tuple):
    inv_string = []
    for cond, cmds in inv_tuple:
        # print("cond is {},cmds is {}".format(cond, cmds))
        inv = ''
        inv = ' & '.join(cond)
        inv += ' -> ' 
        if isinstance(cmds, str):
            inv += cmds 
        else:
            cmd1, cmd2 = cmds
            inv += '(' + ' & '.join(cmd1) + ' -> ' + cmd2 + ')'
        inv_string.append(inv)
    return inv_string

def transform(p, NODE2para_dict={}):
    if NODE2para_dict:
        if p in NODE2para_dict:
            return NODE2para_dict[p]
        else:
            # print('Parameter {} out of range'.format(p))
            return None
    else:
        if p == 'NODE_1':
            return "i"
        elif p == 'NODE_2':
            return "j"
        else:
            # print('Parameter {} out of range'.format(p))
            return None

def to_murphi(inv_name, rule, all_types, NODE2para_dict={}, strengthen = False):
    """
    translate an association rule('Chan2[NODE_1].Cmd = Inv -> Cache[NODE_2].Data = AuxData') into murphi code
    invariant "rule_1"
        forall i: NODE do forall j: NODE do
        (i != j) -> (Chan2[i].Cmd = Inv -> Cache[j].Data = AuxData)
    end end;

    :param rule: an association rule
    :param par: NODE
    :return: murphi code
    """
    # print('paradict in to_murphi is {}'.format(NODE2para_dict))
    pre_paras_dict = {}
    cond_paras_dict = {}
    pre, cond = rule.split('->')[0].strip(), '->'.join(rule.split('->')[1:]).strip()
    #Put the global var and the var with the same idx as pre togother, 
    #and put the another local idx separately
    q_list, p_list = [], []

    for t in all_types:
        # Find NODE_1,NODE_2
        find_result = set(re.findall(r'{}_\d'.format(t), pre))
        # Find_result:['NODE_2', 'NODE_1']
        for result in find_result:
            pre_paras_dict.update({transform(result,NODE2para_dict): t})
            pre = re.sub(result, transform(result, NODE2para_dict),pre)
    for t in all_types:
        # Find NODE_1,NODE_2
        find_result = set(re.findall(r'{}_\d'.format(t), cond))
        for result in find_result:
            if transform(result, NODE2para_dict) not in pre_paras_dict: 
                cond_paras_dict.update({'q': t})
                cond = re.sub(result, 'q', cond)
            else:
                cond = re.sub(result, transform(result, NODE2para_dict), cond)
    
    murphi_string = 'invariant \"{}\"\n'.format(inv_name)

    #Parameter in pre 
    murphi_string += '\nforall ' if pre_paras_dict else ''
    unequal_list, para_list = [], []
    for p, t in pre_paras_dict.items():
        para_list.append('{} : {} '.format(p, t))
    murphi_string += ('do forall '.join(para_list) + 'do\n') if pre_paras_dict else ''

    index = 1
    pre_para_list = list(pre_paras_dict.keys())
    while index < len(pre_paras_dict):
        if pre_paras_dict[pre_para_list[index - 1]] == pre_paras_dict[pre_para_list[index]]:
            unequal_list.append("{} != {}".format(pre_para_list[index - 1], pre_para_list[index]))
        index += 1

    cond_conj = parse_single_inv(cond)
    cond_sep = seperation(cond_conj)
    for cs in cond_sep:
        idx = find_index(cs)
        if str(idx) in pre_para_list or str(cs.expr2) in pre_para_list:
            p_list.append(str(cs))
        else:
            q_list.append(str(cs))

    # Pre is a part of guard
    unequal_string = '\t' + ' & '.join(unequal_list) + '&\n' if unequal_list else ''
    murphi_string += unequal_string  # ('\n\t%s' % unequal_string + '\n\t->\n\t') if unequal_string else ''
    murphi_string += pre + '\n->\n'
    if strengthen:
        murphi_string += '&'.join(p_list)
        murphi_string += '\n&' if len(p_list) != 0 and len(q_list) != 0 else ''
    
    #parameter in cons
    unequal_list, para_list = [], []
    if cond_paras_dict:
        assert len(cond_paras_dict) == 1
        murphi_string += 'forall '
        for p, t in cond_paras_dict.items():
            para_list.append('q : {} '.format(t))
        murphi_string += 'do forall '.join(para_list) + 'do\n'
        if len(pre_paras_dict) == 1:
            unequal_list.append("q != {} ".format(pre_para_list[0]))
    
    unequal_string = '\t' + ' & '.join(unequal_list) + '->\n' if unequal_list else ''   
    murphi_string += unequal_string   
    if strengthen:
        murphi_string += ' & '.join(q_list) + '\n'
    else: 
        murphi_string += ' & '.join([str(cs) for cs in cond_sep]) + '\n'    

    # forall_len = len(pre_paras_dict)+len(cond_paras_dict)
    if len(cond_paras_dict) == 1:
        murphi_string += '\nend' 
    for i in range(len(pre_paras_dict)):
        murphi_string += '\nend' 
    murphi_string += ';\n'
    invs = []
    if strengthen:
        invs = especialForData(murphi_string, inv_name)
    else:
        invs.append(murphi_string)
    return invs

def especialForData(murphi_string, inv_name):
    invs = []
    content = re.findall(r'invariant.*?\n(.*?);', murphi_string, re.S)[0]
    e = inv2OPexpr.parse_single_inv(content)
    if not isinstance(e, murphi.ForallExpr):
        return [murphi_string]
    var_decls = []
    while isinstance(e, murphi.ForallExpr):
        var_decls.append(e.var_decl)
        e = e.expr
    assert isinstance(e, murphi.OpExpr) and e.op == '->', "e.op is{}".format(e.op)
    conds = e.expr2
    cond_list = seperation(conds)
    noData = []
    for cond_expr in cond_list:
        if isinstance(cond_expr, murphi.OpExpr) and isinstance(cond_expr.expr1, murphi.FieldName) and 'DATA' in str(cond_expr.expr1.field).upper():
            data_inv = murphi.OpExpr('->', e.expr1, cond_expr)
            for i in range(len(var_decls)-1, -1, -1):
                data_inv = murphi.ForallExpr(var_decls[i], data_inv)
            invs.append(str(murphi.MurphiInvariant(inv_name, data_inv)))
        else:
            noData.append(cond_expr)
    if len(noData) > 0:
        noData_inv = murphi.OpExpr('->', e.expr1, combine(noData))
        for i in range(len(var_decls)-1, -1, -1):
            noData_inv = murphi.ForallExpr(var_decls[i], noData_inv)
        invs.append(str(murphi.MurphiInvariant(inv_name, noData_inv)))

    return invs

if __name__ == '__main__':
    data_dir = './'
    protocol_name = 'Flash'
    with open('./Flash/auxInvs/auxInvs_NI_Remote_Get_Put.txt','r') as f:
        rulefile = f.read()
        rules = list(re.findall(r'Lemma_\w+:\s*(.*?)\n', rulefile))
    all_types = {'src':'NODE', 'dst': 'NODE'}
    # print(rules)
    with open('./inv-Flash.txt','w') as f:
        for i, r in enumerate(rules):
            inv_name = 'auxinv_%d'%i
            inv = to_murphi(inv_name, r, all_types)
            f.write(inv+'\n')
            