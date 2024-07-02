import copy
import json
import csv
import re
import os
import collections
from analyser import analyzeParams
import murphi
import murphiparser as parser

#将没抽象的规则名字全改为name+_ref
def trans_ref(filename, protocol_name):
    prot = parser.parse_file(filename)
    for k,r in prot.ori_rule_map.items(): 
        if isinstance(r, murphi.MurphiRule):
            r.name = str(r.name) + '_ref'

        elif isinstance(r, murphi.MurphiRuleSet):
            r.rule.name = str(r.rule.name) + '_ref'

    with open('./ref_{}.m'.format(protocol_name), 'w') as f:
        f.write(str(prot))

def cond_dict(paras, is_skip):
    para_dict ={}
    para_list = list(paras.keys())
    if is_skip:
        if len(paras) == 1:
            para_dict.update({para_list[0] : True})
        elif len(paras) == 2:
            para_dict.update({para_list[0] : True, para_list[1] : True})
    else:
        if len(paras) == 1:
            para_dict.update({"cond":{para_list[0] : False},"answer":"skipRule"})
        elif len(paras) == 2:
            para_dict.update({"cond":{para_list[0] : False, para_list[0] : True},"answer":"skipRule"})
            para_dict.update({"cond":{para_list[0] : True, para_list[1] : False},"answer":"skipRule"})
            para_dict.update({"cond":{para_list[0] : False, para_list[1] : False},"answer":"skipRule"})
    return para_dict

def skip_dict(rule_dict, checked, ABS_set):
    if os.path.exists('./ABS_ref_{0}.m'.format(protocol_name)):
        with open('./ABS_ref_{0}.m'.format(protocol_name), 'r') as f:
            text = f.read()
            assert text != ''
    else:
        print('reading ABS_file failed!')
    pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
    rulesets = pattern.findall(text)
    # print('length of rulesets is {}'.format(len(rulesets)))
    for params, rules_str in rulesets:
            param_name_dict , _ = analyzeParams(params)
            # print('param_name_dict is {}'.format(param_name_dict))
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                rulename = re.findall(r'rule\s*\"(.*?)\"\s*.*?==>.*?begin.*?endrule\s*;', each_rule, re.S)[0]
                if 'ABS' not in rulename:
                    temp_name = 'ABS_' + rulename.replace('_ref', '')
                    if  (temp_name not in checked) and (temp_name not in ABS_set):
                        f_dict = cond_dict(param_name_dict, is_skip=False)
                        rule_dict[rulename.replace('_ref', '')]['abstract'].append(f_dict)
                    elif (temp_name not in checked) and (temp_name in ABS_set):
                        rule_dict[rulename.replace('_ref', '')]['abstract'].append(f_dict)
    return rule_dict

def json_str_gen(filename):
    print('you wanna reading {}...'.format(filename))
    prot = parser.parse_file(filename)
    assert isinstance(prot, murphi.MurphiProtocol)
    rule_dict = collections.defaultdict(dict)
    not_skip = set()
    abs2ori = {}

    # record enum info
    enum_type = {'enum_typs':[]}
    for typ_decl in prot.types:
            if isinstance(typ_decl.typ, murphi.EnumType) and str(typ_decl.name) != 'OTHER':
                enum_type['enum_typs'].append(typ_decl.name)

    # obtain frame
    for k,r in prot.ori_rule_map.items(): 
        if isinstance(r, murphi.MurphiRule):
            rule_name = r.name.replace('_ref','')
            rule_dict[rule_name].update({"rule":rule_name})
            rule_dict[rule_name].update({"strengthen":[]})
            rule_dict[rule_name].update({"answer":"{}_ref".format(rule_name)})
            rule_dict[rule_name].update({"abstract":[]})

        elif isinstance(r,murphi.MurphiRuleSet):
            rule_name = r.rule.name.replace('_ref','')
            if len(r.var_decls) == 1:
                rule_dict[rule_name].update({'limits':r.var_map})
                rule_dict[rule_name].update({"ruleset":rule_name})
                rule_dict[rule_name].update({"strengthen":[]})
                rule_dict[rule_name].update({"answer":"{}_ref".format(rule_name)})
                rule_dict[rule_name].update({"abstract":[{"cond": {str(r.var_decls[0].name) : True},"answer":"{}_ref".format(rule_name)}]})
            
            elif len(r.var_decls) == 2:
                rule_dict[rule_name].update({'limits':r.var_map})
                rule_dict[rule_name].update({"ruleset":rule_name})
                rule_dict[rule_name].update({"strengthen":[]})
                rule_dict[rule_name].update({"answer":"{}_ref".format(rule_name)})
                rule_dict[rule_name].update({"abstract":[{"cond": {r.var_decls[0].name : True, r.var_decls[1].name : True},"answer":"{}_ref".format(rule_name)}]})
                if str(r.var_decls[0].typ) == 'DATA' or str(r.var_decls[1].typ) == 'DATA':
                    abs2ori['ABS_'+rule_name] = rule_name
                else:
                    params = list(r.var_map.keys())
                    abs2ori['ABS_'+rule_name+'_'+params[0]] = rule_name
                    abs2ori['ABS_'+rule_name+'_'+params[1]] = rule_name
                    abs2ori['ABS_'+rule_name+'_'+params[0]+'_'+params[1]] = rule_name
    # print(abs2ori)

    # record strengthening info
    for k,r in prot.abs_rule_map.items():
        if isinstance(r,murphi.MurphiRule):
            if r.name in abs2ori:
                rule_name = abs2ori[r.name]
            else:
                rule_name = r.name.replace('ABS_', '')
            print(rule_name)
            not_skip.add(rule_name)
            param = list(rule_dict[rule_name]['limits'].keys())
            if len(param) == 1:
                cond_res = {'i': False}
            elif len(param) == 2:
                cond_res = {param[0]: False, param[1]: False}
            rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer": r.name})

        elif isinstance(r,murphi.MurphiRuleSet):
            rule_name = abs2ori[r.rule.name]
            not_skip.add(rule_name)
            if str(r.var_decls[0].typ) == 'DATA':
                cond_res = copy.deepcopy(rule_dict[rule_name]["abstract"][0]["cond"])
                for decl, typ in prot.ori_rule_map[rule_name+'_ref'].var_map.items():
                    if str(typ) != 'DATA':
                        cond_res.update({str(decl):False})
                rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer":r.rule.name})
            else:
                decl = r.rule.name.split('_')[-1]
                param = list(rule_dict[rule_name]['limits'].keys())
                if len(r.var_decls) == 1:
                    if len(param) == 2:
                        cond_res = copy.deepcopy(rule_dict[rule_name]["abstract"][0]["cond"])
                        print("****", cond_res)
                        cond_res.update({decl:False})
                        rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer":r.rule.name})
                    else:
                        raise ValueError("Len of param must be 2")

                else:
                    raise ValueError("Len of decl is {}".format(len(r.var_decls)))
        else:
            raise ValueError("Wrong murphi rule {}".format(r))

    # print('not skip is {}'.format(not_skip))

    # Add skiprule info
    for k,r in prot.ori_rule_map.items():    
        if isinstance(r,murphi.MurphiRuleSet):
            rule_name = r.rule.name.replace('_ref','')
            if rule_name not in not_skip:
                param = list(rule_dict[rule_name]['limits'].keys())
                if len(param) == 1:
                    # cond_res = {param[0]: False}
                    cond_res = {'i': False}
                    rule_dict[rule_name]["abstract"].append({"cond": cond_res,"answer": "skipRule"})
                elif len(param) == 2:
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: False, param[1]:True},"answer": "skipRule"})
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: True, param[1]:False},"answer": "skipRule"})
                    rule_dict[rule_name]["abstract"].append({"cond": {param[0]: False, param[1]:False},"answer": "skipRule"})
    
    return enum_type, rule_dict

# Adjust Lemma
def inv_2forall(filename, protocol_name):
    print("you wanna reading \"{}\"".format(filename)) 
    prot = parser.parse_file(filename)
    csv_f = open('./{}/abs_process.csv'.format(protocol_name), 'r')
    reader = csv.reader(csv_f)
    abs_result = dict()
    for line in reader:
        for i in range(len(line)):
            if i > 0:
                abs_result[line[i]] = line[0]
    # print(abs_result)
    for name, inv in prot.ori_inv_map.items():
        cnt = 0
        tmp_expr = inv.inv
        while isinstance(tmp_expr, murphi.ForallExpr):
            para_typ = tmp_expr.typ
            tmp_expr = tmp_expr.expr
            cnt += 1
        if cnt == 0:
            temp_inv = murphi.ForallExpr(murphi.MurphiVarDecl('m', para_typ), inv.inv)
            temp_inv = murphi.ForallExpr(murphi.MurphiVarDecl('n', para_typ), temp_inv)
            temp_inv = murphi.MurphiInvariant(name, temp_inv)
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(temp_inv)
        if cnt == 1:
            temp_inv = murphi.MurphiInvariant(name, murphi.ForallExpr(murphi.MurphiVarDecl('m', para_typ), inv.inv))
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(temp_inv)
        else:
            continue
    for name, inv in prot.lemma_map.items():
        cnt = 0
        tmp_expr = inv.inv
        while isinstance(tmp_expr, murphi.ForallExpr):
            para_typ = tmp_expr.typ
            tmp_expr = tmp_expr.expr
            cnt += 1
        rule_name = abs_result[str(name)]
        ruleset = prot.ori_rule_map[rule_name]
        assert isinstance(ruleset, murphi.MurphiRuleSet)
        decl = ruleset.var_decls
        if cnt == 1:
            temp_inv = murphi.MurphiInvariant(name, murphi.ForallExpr(murphi.MurphiVarDecl('m', para_typ), inv.inv))
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(temp_inv)
        elif cnt == 2 and len(decl) == 2 and all(str(d.typ) != 'DATA' for d in decl):
            temp_inv = murphi.MurphiInvariant(name, murphi.ForallExpr(decl[0], murphi.ForallExpr(decl[1], tmp_expr)))
            prot.decls.remove(prot.inv_map[name])
            prot.decls.append(temp_inv)
        else:
            continue
    with open(filename, 'w') as f:
        f.write(str(prot))

if __name__ == "__main__":
    data_dir = '.'
    protocol_name = 'flash'
    #规范协议形式
    inv_2forall(protocol_name)
    #将ABS_ref中的未抽象规则全加上ref
    # trans_ref(data_dir, protocol_name)
    #获取抽象过程
    # csv_f = open('{}/{}/abs_process.csv'.format(data_dir, protocol_name), 'r')
    # reader = csv.reader(csv_f)
    # abs_result = dict()
    # for line in reader:
    #     abs_result[line[0]] = line[1:]

    #生成json信息
    # filename = '{0}/{1}/ABS_ref_{1}.m'.format(data_dir, protocol_name)
    # enum_type, rule_dict = json_str_gen(filename = filename)
    # # info_dict = json_gen(filename='ABS{}.m'.format(protocol_name),rule_dict = rule_dict, abs_result=abs_result)
    # #加上加强的inv
    # data = []
    # data.append(enum_type)
    # for k,v in rule_dict.items():
    #     data.append(v)
    # for d in data:
    #     if 'ruleset' in d:
    #         # if d['ruleset'] in abs_result:
    #         #     d['strengthen'] = list(reversed(abs_result[d['ruleset']]))
    #         del d['limits']
    # with open('{}_str.json'.format(protocol_name), 'w') as f:
    #     json.dump(data, f, indent=4)