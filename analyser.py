from gettext import find
import re
import collections
import time
from process import string2tuple, merge_tuple2string, to_murphi
from inv2OPexpr import parse_single_inv
import murphi



class TypeDef(object):
    """
    Deal with type and const in murphi

    It can deal with the following definition:
        const
            NODE_NUM : 3;
            DATA_NUM : 2;
        type
            NODE : scalarset(NODE_NUM);
            DATA : 1..DATA_NUM;

    and turn it into:
        self.type = {NODE:NODE_NUM, DATA: DATA_NUM}
        self.const = {NODE_NUM : 3, DATA_NUM:2}
        para = ["NODE"] -- because the type used to represent 'processor' is usually used with 'array [__] of'
    """

    def __init__(self, text):
        self.text = text
        self.type = {}
        self.const = {}
        self.para = []
        self.enumvalues = set()
        self.evaluate()

    def evaluate(self):
        self.eval_scalarset()
        self.eval_const()
        self.eval_arr()
        self.evalEnum()
        # print(self.type, self.const, self.para, self.enumvalues)

    def evalEnum(self):
        enums = re.findall(r'(\w*?)\s*:\s*enum\s*\{(.*?)\}\s*;', self.text, re.S)
        for _, vstr in enums:
            values = list(filter(lambda x: x, list(map(lambda y: y.strip(), vstr.split(','))))) #['I', 'T', 'C', 'E']
            for v in values:
                self.enumvalues.add(v)

    def eval_scalarset(self):
        """
        collect types from two kinds of type:
            1. NODE: 1..NODE_NUM
            2. NODE: scalarset(NODE_NUM)

        :param text: murphi description
        :return: NONE
        """
        scalarsets = re.findall(r'(\w*?)\s*:\s*\w+?\s*\.\.\s*(\w+?)\s*;', self.text, re.S)
        scalarsets2 = re.findall(r'(\w*?)\s*:\s*scalarset\((\w+)\)', self.text, re.S)

        self.type.update({name: num for name, num in scalarsets}) 
        self.type.update({name: num for name, num in scalarsets2}) #{'NODE': 'NODENUMS'}

    def eval_arr(self):
        """
        For now, the type that will be used as a represent of a processor usually can be found in form of :
        array [NODE] of ...
        So identifying it using 'array [\w+] of', and check whether it is in self.types.
        :return:
        """
        pattern = re.compile(r'array\s*\[\s?(\w+)\s?\]\s*of\s*.+')
        array = list(set(re.findall(pattern, self.text))) 
        self.para = [a for a in array if a in self.type] #['NODE']

    def eval_const(self):
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', self.text)
        self.const = {v: d for v, d in config}

    def reset_const(self, para, num):
        """
        reset the configuration by the given parameter name and new number
        :param para:
        :param num:
        :return: new murphi description
        """
        para_const = self.type[para]
        self.text = re.sub(r'%s\s?:\s?(\d+?)\s?;' % para_const, r"%s : %d;" % (para_const, num), self.text)
        return self.text


class Field(object):
    def __init__(self):
        self.para_dict = {}
        self.content = []


def seperation(expr):
        if isinstance(expr, murphi.OpExpr) and expr.op == '&':
            sep = []
            expr1, expr2 = expr.expr1, expr.expr2
            sep.append(expr1)
            return sep+seperation(expr2)
        else:
            return [expr]

def normalization(obj):
    """
    normalize guard_obj or action_obj
    :param obj: {i:TYPE_NODE} [n[i].state = invalid]  normalize -->  n[TYPE_NODE_1].state = invalid
    :return: None
    """
    dic = obj.mainfield.para_dict.copy()
    
    text = parse_single_inv(obj.text)
    all_sentence = []
    atom_list = seperation(text)
    for s in atom_list:
        if not isinstance(s, murphi.ForallExpr) and not (isinstance(s, murphi.OpExpr) and s.op == '->'):
            g = str(s)
            if '!' in g and '=' not in g:
                g = re.sub('!','',g)
                g += ' = false' 
            elif '!' not in g and '=' not in g:
                g += ' = true'
            all_sentence.append(re.sub(r'[\(\)]','', g))

    global_dic, _ = number_type(dic)
    obj.normal_guards = norm_rep(global_dic, all_sentence)

def analyse_guard(obj, statesList):
    def find_states(atom):
        atom = norm_rep(global_dic, [atom])[0]
        states = statesList[0]
        tmp = set()
        for i, g in enumerate(states): #找寻数据表头中满足卫式的一项
            if g == atom:
                col = i
                # print('col is{}'.format(col))
                for row in range(1, len(statesList)):
                    if statesList[row][col] == 'True': 
                        tmp.add(row)
            else:
                g = re.sub('=','!=',g)
                if g == atom:
                    col = i
                    for row in range(1, len(statesList)):
                        if statesList[row][col] == 'False': 
                            tmp.add(row)
        print("atom is {}, len: {}".format(atom, len(tmp)))
        return tmp

    def normal_guard(atom):
        if isinstance(atom, murphi.OpExpr) and atom.op in ('=', '!='):
            return find_states(str(atom))

        elif isinstance(atom, murphi.ArrayIndex) or isinstance(atom, murphi.FieldName) or isinstance(atom, murphi.NegExpr):
            if isinstance(atom, murphi.ArrayIndex) or isinstance(atom, murphi.FieldName) or isinstance(atom, murphi.UnknownExpr):
                str_atom = murphi.OpExpr(op='=', expr1=atom, expr2=murphi.BooleanExpr(True))
                
            elif isinstance(atom, murphi.NegExpr):
                if not isinstance(atom.expr, murphi.OpExpr):
                    str_atom = murphi.OpExpr(op='=', expr1=atom.expr, expr2=murphi.BooleanExpr(False))
            
            else:
                str_atom = atom
            
            return find_states(str(str_atom))
        
        elif isinstance(atom, murphi.OpExpr) and atom.op == '&':
            return normal_guard(atom.expr1) & normal_guard(atom.expr2)
            
        elif isinstance(atom, murphi.OpExpr) and atom.op == '->':
            assum = atom.expr1
            if isinstance(assum, murphi.OpExpr) and assum.op in ('=', '!='):
                if assum.op == '=':
                    assum = murphi.OpExpr(op='!=', expr1=assum.expr1, expr2=assum.expr2)
                else:
                    assum = murphi.OpExpr(op='=', expr1=assum.expr1, expr2=assum.expr2)
            if isinstance(assum, murphi.ArrayIndex) or isinstance(assum, murphi.FieldName):
                assum = murphi.OpExpr(op='=', expr1=assum, expr2=murphi.BooleanExpr(False))
            elif isinstance(assum, murphi.NegExpr):
                if not isinstance(assum.expr, murphi.OpExpr):
                    assum = murphi.OpExpr(op='=', expr1=assum.expr, expr2=murphi.BooleanExpr(True))

            return normal_guard(assum) | normal_guard(atom.expr2)

        elif isinstance(atom, murphi.OpExpr) and atom.op == '|':
            return normal_guard(atom.expr1) | normal_guard(atom.expr2)

        elif isinstance(atom, murphi.ForallExpr):
            return normal_guard(atom.expr)

        else:
            print('atom is {}, type : {}'.format(atom, type(atom)))
            raise

    def find_forallexpr(guard, dic):
        if isinstance(guard, murphi.OpExpr) and guard.op not in ('=', '!='):
            find_forallexpr(guard.expr1, dic)
            find_forallexpr(guard.expr2, dic)
        
        elif isinstance(guard, murphi.ForallExpr):
            var, typ = guard.var, guard.typ
            if str(var) not in dic:
                dic.update({str(var) : str(typ)})
        
        else:
            return

    dic = obj.mainfield.para_dict.copy()
    target = collections.defaultdict(set)
    text = parse_single_inv(obj.text)
    find_forallexpr(text, dic)

    atom_list = seperation(text)
    atom_list = list(filter(lambda x : not(isinstance(x, murphi.OpExpr) and x.op == '!=' and str(x.expr1) in dic and str(x.expr2) in dic), atom_list))
    print("guard in encode is {}".format(atom_list))
    print('dict is {}'.format(dic))
  
    global_dic, _ = number_type(dic)

    target_row = set()
    target_row = normal_guard(atom_list[0])
    for i in range(1, len(atom_list)):
        target_row &= normal_guard(atom_list[i])

    if not target_row:
        for k, v in global_dic.items():
            if v == 'NODE_1':
                global_dic[k]='NODE_2'
            elif v == 'NODE_2':
                global_dic[k]='NODE_1'
        target_row = normal_guard(atom_list[0])
        for i in range(1, len(atom_list)):
            target_row &= normal_guard(atom_list[i])
    
    assert target_row

    for r in target_row:
        for c in range(len(statesList[0])):
            target[statesList[0][c]].add(statesList[r][c]) #将满足卫式的整行都加进去
    target_states = [statesList[0]]
    for i in target_row:
        target_states.append(statesList[i])

    return target, target_states

def pair_2_dict(key_dict, value_dict):
    # assert len(key_dict) == len(value_dict)
    new_dict = {}
    # for k, v in zip(key_dict.values(), value_dict.values()):
    for k in value_dict.keys():
        new_dict[key_dict[k]] = value_dict[k]
    return new_dict


def norm_rep(rep_dict, lst):
    norm_lst = []
    for item in lst:
        for p, t in rep_dict.items():
            item = re.sub(r'\b%s\b' % p, t, item)
        norm_lst.append(item)
    return norm_lst

def number_type(origin_dict):
    new_dic, type_count, rev_dic = {}, {}, {}
    for p, t in origin_dict.items():
        if t not in type_count:
            type_count[t] = 1
        else:
            type_count[t] += 1
        new_dic[p] = '%s_%d' % (t, type_count[t])
        rev_dic['%s_%d' % (t, type_count[t])] = p
    return new_dic, rev_dic

class Part(object):
    def __init__(self):
        self.all_sentence = set()
        self.normal_guards = set()
        self.mainfield = Field()
        self.mainfield.para_dict = {}
        self.forfield = []
        self.existfield = []

    def print_value(self, title=""):
        print('\n[%spart]' % title)
        print('- main field: \n\t- parameters: %s\n\t- content:%s' % (self.mainfield.para_dict, self.mainfield.content))
        for item in self.forfield:
            print('- forfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))
        for item in self.existfield:
            print('- existfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))


class Guard(object):
    def __init__(self, text, param_name_dict):
        self.param_name_dict = param_name_dict
        self.text = re.sub(r'--.*', '', text)
        self.all_sentence = set()
        self.normal_guards = set()
        self.mainfield = Field()
        self.mainfield.para_dict = param_name_dict
        self.forfield = []
        self.existfield = []
        # self.sparse()

    def sparse(self):
        def para_repl(match):
            return self.param_name_dict[match.group()] if match.group() in self.param_name_dict else match.group()

        split_guard = list(map(lambda x: x.strip(), self.text.split('&')))
        for g in split_guard:
            if g.startswith(('forall', '!forall')):
                self.deal_forall(g)
            elif g.startswith(('exists', '!exists')):
                self.deal_exist(g)
            else:
                # self.guards.add(re.sub('\w+', para_repl, g))
                self.all_sentence.add(g)
                self.mainfield.content.append(g)

    def deal_forall(self, text):
        pattern = re.compile(r'forall(.*?)do(.*)end', re.S)
        try:
            params, content = re.findall(pattern, text)[0]
        except:
            print('cannot deal with %s ' % text)
        else:
            temp_field = Field()

            param_name_dict, _ = analyzeParams(params)
            temp_field.para_dict = param_name_dict
            # for var, type in param_name_dict.items():
            # parts = set(filter(lambda x: x, map(lambda x: re.sub('%s' % var, type, x.strip()),
            #                 filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content)))))
            parts = set(filter(lambda x: x, map(lambda x: x.strip(),
                                                filter(lambda x: len(x) > 2,
                                                       re.split(r'&', content)))))
            # re.split(r'(\||->|\n|\(|\)|&)', content)))))

            temp_field.content = list(filter(lambda x: x, map(lambda x: x.strip(),
                                                              filter(lambda x: len(x) > 2,
                                                                     re.split(r'&', content)))))
            # re.split(r'(\||->|\n|\(|\)|&)', content)))))
            self.all_sentence |= parts
            self.forfield.append(temp_field)

    def deal_exist(self, text):
        pattern = re.compile(r'!?exists(.*?)do(.*)end', re.S)
        try:
            params, content = re.findall(pattern, text)[0]
        except:
            print('cannot deal with %s ' % text)

        temp_field = Field()
        
        param_name_dict,_ = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        #Python 字典(Dictionary) items() 函数以列表返回可遍历的(键, 值) 元组数组。
        '''
        tinydict = {'Google': 'www.google.com', 'Runoob': 'www.runoob.com', 'taobao': 'www.taobao.com'}
 
        print "字典值 : %s" %  tinydict.items()
 
        # 遍历字典列表
        for key,values in  tinydict.items():
        print (key,values)
        字典值 : [('Google', 'www.google.com'), ('taobao', 'www.taobao.com'), ('Runoob', 'www.runoob.com')]
        Google www.google.com
        taobao www.taobao.com
        Runoob www.runoob.com
        '''
        for var, type in param_name_dict.items(): 
            # for var, type, statesment in forall_parts:
            parts = set(map(lambda x: re.sub(var, type, x.strip()),
                            filter(lambda x: len(x) > 2,
                                   re.split(r'&', content))))  # re.split(r'(\||->|\n|\(|\)|&)', content))))
            temp_field.content = list(map(lambda x: x.strip(),
                                          filter(lambda x: len(x) > 2, re.split(r'&',
                                                                                content))))  # re.split(r'(\||->|\n|\(|\)|&)', content))))
            self.all_sentence |= parts
            self.existfield.append(temp_field)

    def evaluate(self):
        # print('guards here:%s' % self.all_sentence)
        print('\n[Guard part]')
        print('- main field: \n\t- parameters: %s\n\t- content:%s' % (self.mainfield.para_dict, self.mainfield.content))
        for item in self.forfield:
            print('- forfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))
        for item in self.existfield:
            print('- existfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))

    def collect_atoms(self):
        atoms = set()
        dic = self.mainfield.para_dict
        for item in self.forfield:
            dic.update(item.para_dict)
        for item in self.existfield:
            dic.update(item.para_dict)
        for guard in self.all_sentence:
            for k, v in dic.items():
                guard = re.sub(r'\b%s\b' % k, v, guard, re.I)
            atoms.add(guard)
        return atoms


class Action(object):
    def __init__(self, text, param_name_dict):
        self.param_name_dict = param_name_dict
        self.text = text
        self.all_sentence = set()
        self.normal_guards = set()
        self.mainfield = Field()
        self.mainfield.para_dict = param_name_dict
        self.forfield = []
        self.existfield = []
        # self.sparse()

    def sparse(self):
        def para_repl(match):
            return self.param_name_dict[match.group()] if match.group() in self.param_name_dict else match.group()

        self.rm_for()

        split_action = list(filter(lambda x: x, map(lambda x: x.strip(), self.text.split(';'))))

        for a in split_action:
            self.all_sentence.add(a)
            self.mainfield.content.append(a)

    def rm_for(self):
        for_stmt = re.findall(r'(!?for.*?do.*?endfor;)', self.text, re.S)
        for stmt in for_stmt:
            self.deal_for(stmt)
        self.text = re.sub('for(?:.|\n)*do(?:.|\n)*endfor(?:.|\n)*?;', "", self.text, re.S).strip('\n').strip(' ')

    def deal_for(self, text):
        pattern = re.compile(r'!?for(.*?)do(.*)endfor;?', re.S)
        params, content = re.findall(pattern, text)[0]

        temp_field = Field()

        param_name_dict, _ = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        # for var, type in param_name_dict.items():
        parts = set(filter(lambda x: x, map(lambda x: x.strip(),
                                            filter(lambda x: len(x) > 2,
                                                   re.split(';', content)))))
        # re.split(r'(\||->|\n|\(|\)|&|;)', content)))))

        temp_field.content = list(filter(lambda x: x, map(lambda x: x.strip(),
                                                          filter(lambda x: len(x) > 2,
                                                                 re.split(';', content)))))
        # re.split(r'(\||->|\n|\(|\)|&|;)', content)))))
        self.all_sentence |= parts
        self.forfield.append(temp_field)

    def rm_exist(self):
        exist_stmt = re.findall(r'(!?exists.*?do.*endexists.*?;)', self.text, re.S)
        for stmt in exist_stmt:
            self.deal_exist(stmt)
        self.text = re.sub(r'!?exists(.*?)do(.*)(end|endfor);', '', self.text)

    def deal_exist(self, text):
        pattern = re.compile(r'!?exists(.*?)do(.*)end', re.S)
        params, content = re.findall(pattern, text)[0]
        temp_field = Field()

        param_name_dict , _= analyzeParams(params)
        temp_field.para_dict = param_name_dict
        parts = set(map(lambda x: x.strip(),
                        filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
        temp_field.content = list(map(lambda x: x.strip(),
                                      filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
        self.all_sentence |= parts
        self.existfield.append(temp_field)

    def evaluate(self):
        print('\n[Action part]')
        print('- main field: \n\t- parameters: %s\n\t- content:%s' % (self.mainfield.para_dict, self.mainfield.content))
        for item in self.forfield:
            print('- forfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))
        for item in self.existfield:
            print('- existfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))

def inv_strengthen(used_string_list, rule, all_types, NODE2para_dict):
    str_global = []
    str_local = []
    global_idx = []
    local_idx = []
    invs = []
    for i, r in enumerate(used_string_list):
        murphi_strings = to_murphi(inv_name = 'tmp_aux',rule = r, all_types=all_types,NODE2para_dict=NODE2para_dict, strengthen = True)
        for murphi_string in murphi_strings:
            invs.append(murphi_string)
            content = re.findall(r'invariant.*?->\n(.*?);',murphi_string,re.S)[0]
            if 'forall' in content:
                content = re.sub(r'\n\s*end', '', content)
                content += '\nend'
                str_local.append(content)
                local_idx.append(i)
            else:
                content = re.sub(r'\n\s*end', '', content)
                str_global.append(content)
                global_idx.append(i)
    pre = rule.split('==>')[0]
    action = rule.split('==>')[1]
    str_info = pre
    for c in str_global:
        str_info += '& {}'.format(c)
    if len(str_local) != 0:
        str_info += '\n&'
        str_info += '&'.join(str_local)
    str_info += '\n==>\n'
    str_info += action
    return str_info, global_idx + local_idx, invs

class Ruleset(object):
    def __init__(self, data_dir, protocol_name, text, type):
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.text = text
        self.type = type
        self.guards = set()
        self.atoms = set()
        self.print_info = ""
        self.used_inv_string_set = set()
        self.dict_used_inv = {}

    def collect_atoms_from_ruleset(self):
        pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
        rulesets = pattern.findall(self.text)
        for params, rules_str in rulesets:
            param_name_dict,_ = analyzeParams(params)
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                self.collect_atoms_from_rule(each_rule, param_name_dict)

    def collect_atoms_from_rule(self, rule_text, param_name_dict):
        pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
        rule_name, guards, _ = pattern.findall(rule_text)[0]
        guard_obj = Guard(guards, param_name_dict)
        guard_obj.sparse()
        # if guard_obj:
        self.atoms |= guard_obj.collect_atoms()
        # print('collect atoms from %s' % rule_name)

    def sparse_rule(self, rule_text, param_name_dict):
        pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
        rule_name, guards, actions = pattern.findall(rule_text)[0]
        guard_obj = Guard(guards, param_name_dict)
        guard_obj.sparse()
        action_obj = Action(actions, param_name_dict)
        action_obj.sparse()
        return rule_name, guard_obj, action_obj

    def sparse_single_rule(self, aux_invs, flag, boundary_K):
            pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
            rulesets = pattern.findall(self.text)

            for params, rules_str in rulesets:
                param_name_dict , param_name_list= analyzeParams(params)
                rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
                for each_rule in rules:
                    # split rulename, guard part, action part
                    rulename, guards_obj, actions_obj = self.sparse_rule(each_rule, param_name_dict)

                    if rulename == flag:
                        print("\n\n[Rulename]: %s" % rulename)

                        normalization(guards_obj)

                        # refine guard, return useful_invs
                        refiner = Reiner(rulename, guards_obj, aux_invs)
                        useful_invs, _ = refiner.find_useful_invs(boundary_K=boundary_K)
                        start_time = time.time()
                        from collections import defaultdict
                        inv_list = []
                        rule_dict = defaultdict(list)
                        for pre, conse in useful_invs:
                            froze_pre = frozenset(pre)
                            if conse not in rule_dict[froze_pre]:
                                rule_dict[froze_pre].append(conse)
                        for k,v in rule_dict.items():
                            for v1 in v:
                                inv_list.append((k,v1))

                        useful_inv_string = merge_tuple2string(inv_list)

                        end_time = time.time()
                        print("The time spent of simplify is :{}, len: {}".format(str(end_time - start_time), len(useful_inv_string)))

                        with open('{0}/{1}/useful_rule-{2}.txt'.format(self.data_dir, self.protocol_name, flag), 'w') as f:
                            for i, r in enumerate(useful_inv_string):
                                f.write("rule_{}:{}\n".format(i, r))

                        return useful_inv_string

class Reiner(object):
    def __init__(self, rulename, guard_obj, aux_invs):
        self.rulename = rulename
        self.guard_obj = guard_obj
        self.aux_invs = aux_invs
        self.dict_inv2index = {}
        self.dict_index2inv = {}
        self.construct_dicts()
        self.used_inv_index = set()

    def construct_dicts(self):
        print('type fo self.aux_invs = {}'.format(type(self.aux_invs)))
        for i, aux_inv in enumerate(self.aux_invs, 1):
            self.dict_index2inv[i] = aux_inv
            self.dict_inv2index[' & '.join(aux_inv[0]) + ' -> ' + aux_inv[1]] = i

    def map_index_to_inv(self):
        used_inv = []
        for index in self.used_inv_index:
            used_inv.append(self.dict_index2inv[index])
        return used_inv

    def new_inv(self, used_invset):
        guard = list(self.guard_obj.normal_guards)
        for i, g in enumerate(guard):
            if '!' in g and '=' not in g:
                g = re.sub('!','',g)
                g += ' = false' 
                guard[i] = g
            if '!' not in g and '=' not in g:
                g += ' = true'
                guard[i] = g
        guard = list(map(lambda x: re.sub(r'--.*', '', x), guard))
        guard = list(map(lambda x: re.sub(r'\n', '', x), guard))
        guard = set(guard)
        print('guard is :{}'.format(guard))
        new_invset = list()
        cnt = 3
        for pre, conse in used_invset:
            if (pre & guard) != pre:
                conse = (pre-guard,conse)
                new_invset.append((pre & guard,conse))
            elif pre & guard:
                new_invset.append((pre,conse))
        return new_invset

    def find_useful_invs(self, boundary_K, guard=set()):
        if not guard:
            guard = list(self.guard_obj.normal_guards)
            for i, g in enumerate(guard):
                if '!' in g and '=' not in g:
                    g = re.sub('!','',g)
                    g += ' = false' 
                    guard[i] = g
                if '!' not in g and '=' not in g:
                    g += ' = true'
                    guard[i] = g 
            guard = list(map(lambda x: re.sub(r'--.*', '', x), guard))
            guard = list(map(lambda x: re.sub(r'\n', '', x), guard))
            guard = set(guard)

        temp_k = 0
        iter_cons = set()

        for k in range(boundary_K):
            iter_cons |= self.find_useful_invs_iter(guard | iter_cons)
        used_invset = self.map_index_to_inv()
        self.evaluate(used_invset)
        return used_invset, self.used_inv_index

    def find_useful_invs_iter(self, guard):
        useful_cond = set()
        for i, (pre, cond) in enumerate(self.aux_invs, 1):
            if guard & pre == pre:
                useful_cond.add(cond)
                # record used aux invs
                if cond not in set(guard):
                    self.used_inv_index.add(i)
        return useful_cond

    def evaluate(self, used_invset):
        if not used_invset:
            return
        print("\n[Candidate association rules used by {}]: {}".format(self.rulename, len(used_invset)))
        # for i, (pre, cond) in enumerate(used_invset, 1):
        #     print("\t%d: %s -> %s" % (i, ' & '.join(pre), cond))


class Abstractor(object):
    def __init__(self, rulename, guard_obj, action_obj, abs_type, aux_invs, all_types, home_flag, logfile,
                 dict_inv2index):
        self.rulename = rulename
        self.guard_obj = guard_obj
        self.action_obj = action_obj
        self.abs_type = abs_type
        self.home = home_flag
        self.aux_invs = aux_invs
        self.all_types = all_types
        self.print_string = ""
        self.used_inv_string_list = []
        self.logfile = logfile
        self.dict_inv2index = dict_inv2index

    def rep_global(self, aux_inv_list, action_obj, abs_para_list):
        new_action_content = []
        rep_dict, added_dict = {}, {}
        rep_dict_to_string = {}
        rep_index = []

        def check_other_types(all_types, stmt, origin_dict):
            temp_dict = {}
            for t in all_types:
                finds = re.findall(r'%s\_\d' % t, stmt)
                for find in finds:
                    if find not in origin_dict:
                        temp_dict[find] = t
            return temp_dict

        for pre, cond in aux_inv_list:
            if not pre or not cond: continue
            if re.findall('!', cond):
                continue
            parts = re.split(r'\s=\s', cond)
            # print('cond = {}, part = {}'.format(cond, parts))

            left, right = parts[0], parts[1]
            if not re.findall(r'\[', right):
                rep_dict[left] = right
                rep_dict_to_string[left] = (' & '.join(pre) + ' -> ' + ''.join(cond))

        is_repl = False
        for stmt in list(filter(lambda x: re.findall(':=', x), action_obj.mainfield.content)):
            assign = re.split(r':=\s*.*?', stmt)[1]
            for abs_para in abs_para_list:
                if re.findall(r'%s' % abs_para, assign):
                    if assign in rep_dict:
                        # is_repl = True
                        stmt = stmt.replace(assign, rep_dict[assign])
                        added_dict.update(check_other_types(self.all_types, stmt, self.action_obj.mainfield.para_dict))
                        self.used_inv_string_list.append(rep_dict_to_string[assign])
                        rep_index.append(self.dict_inv2index[rep_dict_to_string[assign]])
                        # open(self.logfile, 'a').write(
                        #     'replace: {}\n'.format(self.dict_inv2index[rep_dict_to_string[assign]]))

            new_action_content.append(stmt)
        # if not is_repl:
        #     open(self.logfile, 'a').write('rule used for replace: []\n')
        self.action_obj.mainfield.content = new_action_content
        self.action_obj.mainfield.para_dict.update(added_dict)

        return rep_index

def analyzeParams(params):
    """
    @param params: as `i:Node; j:Node`
    @return a tuple as `{'i': 'Node', 'j': 'Node'}
    """
    if not params: return {}, '[]'
    parts = params.split(';')
    param_name_dict = {}
    para_name_list = []
    for p in parts: 
        param_name_dict[p.split(':')[0].strip()] = p.split(':')[1].strip()
        para_name_list.append(p.split(':')[0].strip())

    return param_name_dict, para_name_list


class Protocol(object):
    def __init__(self, data_dir, protocol_name, file_url): #data_dir = './protocols';file_url = '{0}/{1}/{1}.m'.format(data_dir, args.protocol)
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.file_url = file_url
        self.logfile = '{}/{}/prot.abs'.format(self.data_dir, self.protocol_name)

    def read_file(self):
        return open(self.file_url).read()

    def show_config(self):
        text = self.read_file()
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', text)
        for name, num in config:
            print('{} : {}'.format(name, num))

    def collect_atoms(self):
        text = self.read_file()
        typedf = TypeDef(text)
        ruleset = Ruleset(self.data_dir, self.protocol_name, text, typedf.para)
        ruleset.collect_atoms_from_ruleset()
        return typedf.type

    def find_rule(self, aux_invs, flag, boundary_K=1):
        text = self.read_file()
        # text = re.sub("--.*\n", '', text)
        typedf = TypeDef(text)
        ruleset = Ruleset(self.data_dir, self.protocol_name, text, typedf.type.keys())
        used_invs = ruleset.sparse_single_rule(aux_invs, flag, boundary_K)
        return ruleset.print_info, used_invs
    
if __name__ == "__main__":
    # protocol_name = 'FLASHData'
    protocol_name = 'MutualExData'
    data_dir = '.'
    prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir, protocol_name))
    # flaglist = ['Store', 'NI_Remote_Get_Put', 'PI_Remote_PutX',  'NI_Remote_GetX_PutX', 'NI_Remote_GetX_Nak', 'NI_Local_GetX_PutX2', 'NI_Remote_Get_Nak', 'NI_Local_GetX_GetX', 'NI_InvAck1', 'NI_Remote_GetX_PutX_Home', 'NI_Remote_Get_Put_Home']
    flaglist = ['Store', 'Idle']
    for flag in flaglist:
        print("reading assoRules_{}".format(flag))
        with open('./{}/assoRules/assoRules_{}.txt'.format(protocol_name,flag), 'r') as f:
            rulefile = f.read()
        rules = list(re.findall(r'rule_\w+:\s*(.*?)\n', rulefile))
        ruletuple = string2tuple(rules)
        # print(ruletuple[0])
        _, _ = prot_analyzer.find_rule(ruletuple, flag, boundary_K=1)