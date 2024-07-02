import re
import collections
import sys
import getopt
import os
import joblib
import subprocess
import pandas as pd
import time
import csv
from analyser import Guard, Protocol, analyzeParams, analyse_guard

def split_string_to_tuple(stmt):
    if not stmt:
        return (set(), '')
    try:
        parts = stmt.split(' -> ') #Python split() 通过指定分隔符对字符串进行切片，如果参数 num 有指定值，则分隔 num+1 个子字符串
    except ValueError: #发生异常时打印以下内容
        print('Error string: %s' % stmt)
    else:   #未发生异常执行以下程序
        if not len(re.findall(' & ', parts[0])): #找到所有part[0]中的'&'并统计长度
            return (set([parts[0]]), parts[1])
        else:
            return (set(parts[0].split(' & ')), parts[1])

class DataProcess(object): #data_dir = './protocols'
    def __init__(self, data_dir, name, replace_index, atom_formulas=set(), has_atom=False):
        self.data_dir = data_dir
        self.name = name
        self.replace_index = replace_index
        self.atom_formulas = self.get_atoms(atom_formulas)
        self.has_atom = os.path.exists("{}/{}/atom.txt".format(self.data_dir, self.name)) or has_atom
        # print(self.replace_index)

    def read_trans(self):
        dataList, stateDict = self.read_trans_dataset()
        para_digit = self.para_form(stateDict.keys())
        dataset, itemMeaning = self.state2num_trans(dataList, stateDict)
        return dataset, itemMeaning, para_digit
    
    def getguard(self, name):
        print('from rule {} get guard'.format(name))
        prefix_filename = '{0}/{1}/{1}'.format(self.data_dir, self.name)
        txt_filename = prefix_filename + '.m'
        rule_txt = open(txt_filename).read()
        pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
        rulesets = pattern.findall(rule_txt)
        for params, rules_str in rulesets:
            param_name_dict, _ = analyzeParams(params)
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                # print(each_rule)
                pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
                rule_name, guards, _ = pattern.findall(each_rule)[0]
                if rule_name == name:
                    return guards, param_name_dict
        print("No guard found")
        return None, {}

    def exe_single(self, para_name_dict=None, guard=None):
        # print('dataList is {}; stateDict is {}'.format(dataList, stateDict))
        dataset, itemMeaning = self.single_encode(para_name_dict, guard)
        # print('Reachable set: %d' % len(dataset))
        print('size of dataset: {} * {}'.format(len(dataset), len(dataset[0])))
        return dataset, itemMeaning
    
    def single_encode(self, para_name_dict, guard):
        if os.path.exists('./{0}/{0}_reach.csv'.format(self.name)) and os.path.exists('./{0}/AllDataSet.csv'.format(self.name)): 
            print('reading states from trans_dataset.csv in dir ./{}'.format(self.name))
            statesList = []
            cnt = 0
            csv_f = open('./{}/AllDataSet.csv'.format(self.name), 'r')
            reader = csv.reader(csv_f)
            for line in reader:
                statesList.append([])
                for i in range(len(line)):
                    statesList[cnt].append(line[i])
                cnt += 1
        else:    
            dataList, stateDict = self.collect_dataset()
            statesList, statesDict = self.atom_feature(stateDict, dataList)
        assert statesList != []
        target = collections.defaultdict(set)

        guard_obj = Guard(guard, para_name_dict)
        guard_obj.sparse()
        target, target_states = analyse_guard(guard_obj, statesList)

        mappingDict, itemMeaning = self.states2num_atom(target)
        # print('mappingDict is {}; itemMeaning is {}'.format(mappingDict, itemMeaning))
        states_numberful = self.mapStates(mappingDict, target_states)
        # print('states_numberful is {}'.format(states_numberful))
        return states_numberful, itemMeaning


    def para_form(self, name_list):
        """
        the parameter the protocol uses
        with symmetry reduction: NODE_1, NODE_2, ...
        without: 1, 2, ...
        '[]' is a symbol of local variables
        :param name_list:
        :return:
        """
        for name in name_list:
            if '[' in name:
                return False if re.search(r'\w+\_\d', name) else True
            continue
        return True

    def collect_dataset(self):
        """
        From reachable set collect dataset
        :return:
        dataList:
            [
                [v1, v2, ..., vn],
                [e11, e12, ..., e1n],
                ...,
                [en1,en2, ..., enn]]
        dataDict:
            {v1: {e11,e21,..., en1}, v2: {e12,e22, ..., en2},...}
        """
        print('Reading reachable set')
        return self.txt2csv()

    def is_rs_match_dataset(self):
        """
        Counts the number of states in reachable set printed by Murphi and the number of lines in transferred csv.
        If these two equal, return True; else return False

        NOTE: actually csv file will add a title line with variable names, so # states in txt +1 = # lines in csv
        """
        print('call is_rs_match_dataset')
        filename = '{0}/{1}/{1}'.format(self.data_dir, self.name)
        if not os.path.exists("{}.txt".format(filename)):
            print('Cannot find reachable state set file. \nNot sure whether the reachable set matches the protocol.')
            return True

        csv_cnt = subprocess.check_output(['wc', '-l', '{}.csv'.format(filename)]).decode('utf-8')
        tail_rs = subprocess.check_output(['tail', '{}.txt'.format(filename)]).decode('utf-8')
        return int(re.findall(r'\d+', csv_cnt)[0]) == int(
            re.findall(r'State Space Explored:.*?(\d+)\sstates', tail_rs, re.S)[0]) + 1

    def readcsv(self, input_file=""):
        print('call read_csv')
        input_file = '{0}/{1}/{1}.csv'.format(self.data_dir, self.name) if not input_file else input_file
        df = pd.read_csv(input_file)
        stateDict = {}
        booleandf = set(df.select_dtypes(include=[bool]).columns.values)

        for col in df.columns:
            if col in booleandf:
                df[col] = df[col].map({True: 'true', False: 'false'})
            stateDict[col] = set(df[col])
        return [df.columns.tolist()] + df.values.tolist(), stateDict

    def read_trans_dataset(self):
        print('call trans_dataset')
        df = pd.read_csv('{}/{}/trans_dataset.csv'.format(self.data_dir, self.name))
        stateDict = {}
        booleandf = set(df.select_dtypes(include=[bool]).columns.values)

        for col in df.columns:
            if col in booleandf:
                df[col] = df[col].map({True: 'true', False: 'false'})
            stateDict[col] = set(df[col])
        return [df.columns.tolist()] + df.values.tolist(), stateDict

    def txt2csv(self):
        print('txt2csv...')
        prefix_filename = '{0}/{1}/{1}'.format(self.data_dir, self.name)
        csv_filename = prefix_filename + '_reach.csv'
        txt_filename = prefix_filename + '_reach.txt'
        reachset = open(txt_filename).read()

        if self.replace_index:
            for k, v in self.replace_index.items():
                print('replace %s by %s' % (k, v))
                reachset = reachset.replace(k, v)
        states = re.findall(r'State\s\d+:\n(.*?)\n\n', reachset, re.S)

        variables = [var.split(':')[0] for var in states[0].split('\n')]

        dataset = [variables]
        open(csv_filename, 'w').write("{}\n".format("".join(variables)))

        stateDict = collections.defaultdict(set)

        for state in states:
            for var in state.split('\n'):
                stateDict[var.split(":")[0]].add(var.split(":")[1])
            dataset.append([var.split(':')[1] for var in state.split('\n')])

        with open(csv_filename, 'w') as f:
            for line in dataset:
                f.write(','.join(line) + '\n')
        return dataset, stateDict

    def describe(self, dataList):
        print('---------------------')
        print('Protocol {} has {} states.'.format(self.name, len(dataList) - 1))
        print('Each state has {} variables.'.format(len(dataList[0])))
        print('---------------------\n')

    def encode_dataset(self, dataList, stateDict):
        dataset, itemMeaning = self.tonumber(dataList, stateDict, atom=self.has_atom, neg=False)

        return dataset, itemMeaning

    def tonumber(self, stateList, statesDict, trans=True, atom=False, neg=False):
        if atom:
            stateList, statesDict = self.atom_feature(statesDict, stateList)
            print("statelist is {}\nstatesDict is {}".format(stateList,statesDict))
            mappingDict, itemMeaning = self.states2num_atom(statesDict)
        elif neg:
            stateList, statesDict = self.negative(stateList, statesDict)
            mappingDict, itemMeaning = self.states2num(statesDict)
        else:
            mappingDict, itemMeaning = self.states2num(statesDict)
        states_numberful = self.mapStates(mappingDict, stateList)

        return states_numberful, itemMeaning

    def enumerateStates(self, stateslist):
        statesDict = collections.defaultdict(set)
        col = len(stateslist[0])
        row = len(stateslist)
        for c in range(col):
            for r in range(1, row):
                if (stateslist[r][c] not in statesDict[stateslist[0][c]]) and (stateslist[r][c] != 'Undefined'):
                    statesDict[stateslist[0][c]].add(stateslist[r][c])
        return statesDict

    def atom_feature(self, stateDict, stateList):#atom.txt在每个状态下的true or false
        new_statelist, new_stateDict = [], {}
        # print("state_list is {}".format(stateList))
        index = {title: i for i, title in enumerate(stateList[0])}
        # print('\nIndex of atomic predicates:', index)

        for i, af in enumerate(self.atom_formulas):
            pre = af.split(' ')[0]
            post = af.split(' ')[-1]
            if pre not in index:
                sys.stderr.write('Cannot find %s in Index' % pre)
                sys.exit()

            col = index[pre] #index[NODE_1] = 0
            cur = [af] #['n[NODE_1] = C']

            for row in range(1, len(stateList)):
                if post not in index:  # in stateDict[pre]:
                    cur.append(str(post == stateList[row][col]))
                else:
                    if post in index:
                        col_post = index[post]
                        if stateList[row][col] != 'Undefined' and stateList[row][col_post] != 'Undefined':
                            cur.append(str(stateList[row][col_post] == stateList[row][col]))
                        else:
                            cur.append('Undefined')
                    else:
                        cur = []
                        break
            if cur:
                new_statelist.append(cur)
                new_stateDict[af] = {x for x in cur} - {af}
        # print("new_statelist is {}".format(new_statelist))
        t_statelist = list(list(i) for i in zip(*new_statelist))
        # print("t_statelist is {}".format(t_statelist))
        assert len(new_statelist) == len(t_statelist[0])
        assert len(new_statelist[0]) == len(t_statelist)

        with open('{}/{}/AllDataSet.csv'.format(self.data_dir, self.name), 'w') as f:
            for state_line in t_statelist:
                f.write('{}\n'.format(','.join(state_line)))

        print("Features / Atomic predicates: % d " % len(self.atom_formulas))
        return t_statelist, new_stateDict

    def state2num_trans(self, stateList, statesDict):
        dataset = stateList
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v in ('true', 'True'):
                    itemMeaning[cnt] = key
                if v in ('false', 'False'):
                    itemMeaning[cnt] = '!' + key
                newDict[key][v] = cnt
                cnt += 1

        state_numberful = self.mapStates(newDict, dataset)

        return state_numberful, itemMeaning

    def states2num_atom(self, statesDict):
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v == 'Undefined':
                    continue
                lower_key = key.lower()
                if 'true' in lower_key or 'false' in lower_key:
                    if 'true' in lower_key:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('true', 'false', key)
                    else:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('false', 'true', key)
                else:
                    if v.lower() == 'false':
                        itemMeaning[cnt] = re.sub(r'=', '!=', key)
                    else:
                        itemMeaning[cnt] = key

                newDict[key][v] = cnt
                cnt += 1

        # print('ItemMeaning:', itemMeaning)
        # for key, value in itemMeaning.items():
        #     print(key, value)
        print('Total products in rs: %d ' % len(itemMeaning))
        return newDict, itemMeaning

    def states2num(self, statesDict):
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v == 'Undefined':
                    continue
                if '!' in v:
                    itemMeaning[cnt] = key + ' != ' + v[1:]
                else:
                    itemMeaning[cnt] = key + ' = ' + v
                newDict[key][v] = cnt
                cnt += 1

        print('\nTotal products in rs: %d \n---------------------------' % len(itemMeaning))

        return newDict, itemMeaning

    def mapStates(self, mappingDict, stateList):
        print('Mapping states into numbers using all variables...')
        states_numberful = []
        for r in range(1, len(stateList)):
            temp = set()
            for c in range(len(stateList[0])):
                if stateList[r][c] != 'Undefined':
                    temp.add(mappingDict[stateList[0][c]][stateList[r][c]])
            states_numberful.append(temp)

        print('successfully mapped!')
        return states_numberful

    def get_atoms(self, atom_formulas):
        if atom_formulas:
            return atom_formulas
        else:
            file_name = "{}/{}/atom.txt".format(self.data_dir, self.name)

            return set(filter(lambda x: x,
                              map(lambda x: re.sub(r'[()]', '', x.strip()), open(file_name, 'r').read().split("\n"))))

    def select_global(self, itemMeaning):
        global_vars = set()
        for k, v in itemMeaning.items():
            if not re.search('[\[\]]', v):
                global_vars.add(k)
        return global_vars

    def negative(self, stateList, statesDict):
        for i in range(1, len(stateList)):
            n = len(stateList[i])
            for j in range(n):
                vals = statesDict[stateList[0][j]]
                if len(vals) <= 2:
                    continue
                for v in vals:
                    if i == 1:
                        stateList[0].append(stateList[0][j])
                    stateList[i].append(v if v == stateList[i][j] else '!' + v)

        statesDict2 = self.enumerateStates(stateList)
        return stateList, statesDict2    

class RuleLearing(object): #新式类 1. 所有类的类型都是type 2. 所有类调用的结果都是构造，返回这个类的实例 3. 所有类都是object的子类 4. 新式类不仅可以用旧类调用父类的方法，也可以用super方法。
    def __init__(self, data_dir, protocol_name, dataset, itemMeaning, global_vars=set(), max_freq_size=3, min_support=0.0,
                 min_confidence=1.0):
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.dataset = dataset
        self.global_vars = global_vars
        self.itemMeaning = itemMeaning
        self.max_freq_size = max_freq_size
        self.min_support = min_support
        self.min_confidence = min_confidence
        self.d_super_set = collections.defaultdict(set) #defaultdict类的初始化函数接受一个类型作为参数，当所访问的键不存在的时候，可以实例化一个值作为默认值

    def execute(self, flag):
        L, support_data = self.apriori(self.global_vars)
        bigRuleList = self.generateRules(L, support_data)
        rule_tuple, rule_string_list = self.prntRules(bigRuleList, flag)
        return rule_tuple, rule_string_list

    def symmetry_reduction(self, rule_tuple, rule_string_list, all_types):
        print('Symmetry reducing rules...')

        min_rule_tuple, min_rule_string_list = [], []
        for (pre, cond), rule_string in zip(rule_tuple, rule_string_list):
            pre_var_set = set(map(lambda x: x.split(' ')[0], pre))
            cond_var = cond.split(' ')[0]
            if cond_var not in pre_var_set:
                min_rule_tuple.append((pre, cond))
                min_rule_string_list.append(rule_string)
        print('Remove redundant: before : {}, after: {}'.format(len(rule_tuple), len(min_rule_tuple)))

        rule_string_set = set(min_rule_string_list)

        for rule_string in min_rule_string_list:
            for t in all_types:
                tmp_stmt = rule_string
                cur_t_set = set(re.findall('%s_\d' % t, rule_string))
                if len(cur_t_set) == 0:  # not contain type parameter
                    continue
                elif len(cur_t_set) == 1:
                    # 含一种type parameter, such as 'NODE_1'
                    if '%s_1' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_1' % t, '%s_2' % t, rule_string)
                    elif '%s_2' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_2' % t, '%s_1' % t, tmp_stmt)
                    else:
                        print('%s contains too many parameters!' % tmp_stmt)

                    if tmp_stmt in rule_string_set:
                        if rule_string in rule_string_set:
                            rule_string_set.remove(rule_string)

                elif len(cur_t_set) == 2:
                    # 含2种type parameter, such as 'NODE_1' and 'NODE_2'
                    cur_t_dict = {}
                    for i, cur_t in enumerate(cur_t_set):
                        cur_t_dict['REP_X_%d' % i] = cur_t
                        tmp_stmt = re.sub(cur_t, 'REP_X_%d' % i, tmp_stmt)
                    for k, v in cur_t_dict.items():
                        tmp_stmt = re.sub(k, (cur_t_set - set([v])).pop(), tmp_stmt)
                    if tmp_stmt in rule_string_set:
                        if rule_string in rule_string_set:
                            rule_string_set.remove(rule_string)
                else:
                    print('Too many types of parameters!')

        sym_red_rule_string = list(rule_string_set)
        sym_red_rule_tuple = list(map(lambda x: split_string_to_tuple(x), sym_red_rule_string))
        assert len(sym_red_rule_string) == len(sym_red_rule_tuple)

        print('Reduction result: before : {}, after: {}'.format(len(min_rule_tuple), len(sym_red_rule_tuple)))
        return sym_red_rule_tuple, sym_red_rule_string

    def instantiate(self, rule_tuple, rule_string_list, all_types):
        print('Instantiating rules...')

        rule_string_set = set(rule_string_list)

        try:
            for rule_string in rule_string_list:
                for t in all_types:
                    tmp_stmt = rule_string
                    cur_t_set = set(re.findall('%s\_\d' % t, rule_string))
                    if len(cur_t_set) == 0:  # not contain type parameter
                        continue
                    elif len(cur_t_set) == 1:  # 含一种type parameter, such as 'NODE_1'
                        if '%s_1' % t in tmp_stmt:
                            tmp_stmt = re.sub('%s_1' % t, '%s_2' % t, rule_string)
                        elif '%s_2' % t in tmp_stmt:
                            tmp_stmt = re.sub('%s_2' % t, '%s_1' % t, tmp_stmt)
                        else:
                            print('Too many parameters!')
                        if tmp_stmt not in rule_string_set:
                            rule_string_set.add(tmp_stmt)
                    elif len(cur_t_set) == 2:  # 含2种type parameter, such as 'NODE_1' and 'NODE_2'
                        cur_t_dict = {}
                        for i, cur_t in enumerate(cur_t_set):
                            cur_t_dict['REP_X_%d' % i] = cur_t
                            tmp_stmt = re.sub(cur_t, 'REP_X_%d' % i, tmp_stmt)
                        for k, v in cur_t_dict.items():
                            tmp_stmt = re.sub(k, (cur_t_set - set([v])).pop(), tmp_stmt)
                        if tmp_stmt not in rule_string_set:
                            rule_string_set.add(tmp_stmt)
                    else:
                        print('Too many types of parameters!')
        except getopt.GetoptError:
            sys.stderr.write('Cannot instantiation, skip')

        sym_expan_rule_string = list(rule_string_set)
        sym_expan_rule_tuple = list(map(lambda x: split_string_to_tuple(x), sym_expan_rule_string))
        assert len(sym_expan_rule_string) == len(sym_expan_rule_tuple)
        print('Expansion result: before : {}, after: {}'.format(len(rule_tuple), len(sym_expan_rule_tuple)))

        # print(type(sym_expan_rule_tuple))
        return sym_expan_rule_tuple, sym_expan_rule_string

    def minimize_rule(self, rest_rule_tuple):
        print('Minimizing rules..')
        fout = '{}/{}/min_rule.txt'.format(self.data_dir, self.protocol_name)
        rest_rule_tuple = sorted(rest_rule_tuple, key=lambda x: len(x[0]))

        left, right = [], []
        for pre, cond in rest_rule_tuple:
            left.append(list(pre))
            right.append(cond)

        same_right = collections.defaultdict(list)
        for l, r in zip(left, right):
            same_right[r].append(l)

        for r, left_list in same_right.items():
            index = [x for x in range(len(left_list))]
            for i in range(len(left_list)):
                for j in range(i + 1, len(left_list)):
                    if j not in index: continue
                    if not (set(left_list[i]) - set(left_list[j])):
                        index.remove(j)
            same_right[r] = [left_list[i] for i in index]

        min_rule_string, min_rule_tuple = [], []

        for r, left_list in same_right.items():
            for l in left_list:
                # if left part doesn't contain array variable, then continue
                if not re.search('[\[\]]', ''.join(l)):
                    continue
                min_rule_tuple.append((set(l), r))
                min_rule_string.append('{} -> {}'.format(' & '.join(l), r))

        with open(fout, 'w') as f:
            for cnt, stmt in enumerate(min_rule_string, 1):
                f.write('rule_%d: %s\n' % (cnt, stmt))

        print('Before: {}, After: {}'.format(len(rest_rule_tuple), len(min_rule_tuple)))
        return min_rule_tuple, min_rule_string

    def createC1(self, dataSet):  # creat candidates frequent set with 1 element
        C1 = []
        for transaction in dataSet:
            for item in transaction:
                if [item] not in C1:
                    C1.append([item]) #'int' object is not iterable

        C1.sort()
        return list(map(frozenset, C1))  # use frozen set so we can use it as a key in a dict

    def scanD(self, D, Ck, minSupport):
        print("len d: {}, len ck:{} ".format(len(D), len(Ck)))
        print("time complexity will be: O({})".format(len(D) * len(Ck)))

        ssCnt = {}
        for key in Ck:
            can = list(key)
            res = self.d_super_set[can[0]] #d_super_set记录了某个元素出现的次数（用集合表示，集合长度就是出现次数）
            for t in can[1:]:
                res = res & self.d_super_set[t] #共同共出现的次数
            if len(res) != 0:
                ssCnt[key] = len(res)

        numItems = float(len(D))
        retList = []
        supportData = {}
        for key in ssCnt:
            support = ssCnt[key] / numItems
            if support >= minSupport:
                retList.append(key)
            supportData[key] = support
        return retList, supportData

    def _build_trie(self, data, k):
        root = {}
        for i, row in enumerate(data):
            row = sorted(list(row))[:k - 2]
            cur = root
            for d in row:
                if d not in cur:  #cur是字典（指向root），判断d是否是cur的键
                    cur[d] = {}
                cur = cur[d] #cur又指向了root中的一个键值
            cur[i] = None
            #最终得到结果如：root is : {'l1': {0: None, 4: None, 5: None, 6: None}, 'l3': {1: None, 2: None}, 'l2': {3: None, 8: None}, 'l4': {7: None}}
        return root

    def aprioriGen(self, Lk, k):  # creates Ck
        retList = []
        root = self._build_trie(Lk, k)
        for i, row in enumerate(Lk):
            row = sorted(list(row))[:k - 2]
            cur = root
            ok = True
            for d in row:
                if d not in cur:
                    ok = False
                    break
                cur = cur[d]
            if ok:
                retList.extend([Lk[i] | Lk[j] for j in cur.keys() if i < j]) #和其它set进行并操作
                #cur.keys()结果如：dict_keys([3, 8, 9])
        return retList

    def _build_super_set(self, data: list):
        """
        :param data: [set,set..]
        :return:
        """
        print('---build_super_set----')
        for i, d in enumerate(data):
            for x in d:
                self.d_super_set[x].add(i) #在set中添加出现时的i

        print('build_super_set done')

    def apriori(self, global_vars):
        print('--------------------------\nGenerating frequent set........')
        start_freq = time.time()
        C1 = self.createC1(self.dataset)
        D = list(map(set, self.dataset))  # add cast to list. In py3, map create a genarator.

        self._build_super_set(D)

        start = time.time()
        L1, supportData = self.scanD(D, C1, self.min_support)
        print('time for scan L1: %.3f' % (time.time() - start))

        L = [L1]
        k = 2
        while k <= self.max_freq_size:
            Ck = self.aprioriGen(L[k - 2], k)
            start = time.time()

            # remove those 3 global variables if minimize = True
            Ck = filter(lambda x: len(x & global_vars) < 3, Ck)  # if is_minimize else Ck

            all_lemma_set = list(Ck)
            Lk, supK = [], {}

            for t in [self.parellel_cal(D, all_lemma_set, self.min_support)]:
                Lk.extend(t[0])
                supK.update(t[1])

            print('time for scan L%d : %.3f\n-------------------\n' % (k, time.time() - start))

            supportData.update(supK)
            L.append(Lk)
            k += 1

        print('Running time for frequent sets: %.3f s' % (time.time() - start_freq))
        return L, supportData

    def parellel_cal(self, D, Ck, minSupport):
        Lk, supK = self.scanD(D, Ck, minSupport)  # scan DB to get Lk
        return (Lk, supK)

    def generateRules(self, L, supportData, minConf=1.0):  # supportData is a dict coming from scanD
        start = time.time()

        bigRuleList = []
        for i in range(1, len(L)):  # only get the sets with two or more items
            for freqSet in L[i]:
                H1 = [frozenset([item]) for item in freqSet]
                if i > 1:
                    self.rulesFromConseq(freqSet, H1, supportData, bigRuleList, minConf)
                else:
                    self.calcConf(freqSet, H1, supportData, bigRuleList, minConf)

        print('Running time for calculating association rules: %.3f s ' % (time.time() - start))

        return bigRuleList

    def calcConf(self, freqSet, H, supportData, brl, minConf=1.0):
        prunedH = []  # create new list to return

        for cond in H:
            conf = supportData[freqSet] / supportData[cond]  # calc confidence
            if conf >= minConf:
                if len(freqSet - cond) == 1:
                    brl.append((cond, freqSet - cond, conf))
                prunedH.append(cond)

        return prunedH

    def rulesFromConseq(self, freqSet, H, supportData, brl, minConf=1.0):
        m = len(H[0])
        if (len(freqSet) > (m + 1)):  # try further merging
            Hmp1 = self.aprioriGen(H, m + 1)  # create Hm+1 new candidates

            Hmp1 = self.calcConf(freqSet, Hmp1, supportData, brl, minConf)

            if (len(Hmp1) > 1):  # need at least two sets to merge
                self.rulesFromConseq(freqSet, Hmp1, supportData, brl, minConf)

    def prntRules(self, bigRuleList, flag):
        if not os.path.exists('{}/{}/assoRules/'.format(self.data_dir, self.protocol_name)):
            os.mkdir('{}/{}/assoRules/'.format(self.data_dir, self.protocol_name))
        ar_filename = '{}/{}/assoRules/assoRules_{}.txt'.format(self.data_dir, self.protocol_name, flag)

        rule_tuple, rule_string_list = [], []

        for ruleTup in bigRuleList:
            ant, conseq = ruleTup[0], ruleTup[1]
            e_ant = set(self.itemMeaning[a] for a in ant)
            e_conseq = list(self.itemMeaning[c] for c in conseq)
            rule_tuple.append((e_ant, e_conseq[0]))
            rule_string_list.append(' & '.join(e_ant) + ' -> ' + ''.join(e_conseq))

        # prot_analyzer = Protocol(self.data_dir, self.protocol_name, '{0}/{1}/{1}.m'.format(self.data_dir, self.protocol_name))
        # all_types = prot_analyzer.collect_atoms()
        # instan_rule_tuple, instan_rule_string = self.instantiate(rule_tuple, rule_string_list, all_types)
        print('\n\nAssociation rules: {}'.format(len(rule_string_list)))
        with open(ar_filename, 'w') as fw:
            for i, rule in enumerate(sorted(rule_string_list, key=lambda x: len(x)), 1):
                fw.write('rule_%d: %s\n' % (i, rule))

        return rule_tuple, rule_string_list

    def slct_rules_by_guards(self, rules_map, guards, par, save=True, load=False):
        if load and os.path.exists("{}/data/norm_rule_dict.pkl".format(self.name)) and os.path.exists(
                "{}/data/rules.pkl".format(self.name)):
            return joblib.load("{}/data/norm_rule_dict.pkl".format(self.name)), joblib.load(
                "{}/data/rules.pkl".format(self.name))

        par = par[0]
        if guards:
            norm_rule_dict = {key: rules for key, rules in rules_map.items() if set(key).issubset(guards)}
        else:
            norm_rule_dict = {key: rules for key, rules in rules_map.items()}

        rules = set()

        for ant_dict in norm_rule_dict.values():
            for ant, conse_set in ant_dict.items():
                for conse in conse_set:
                    line = "{} -> {}".format(' & '.join(sorted(ant)), conse)
                    search_para = re.search(r'%s\_\d' % par, line)

                    cnt = 1
                    while search_para:
                        line = re.sub(search_para.group(), 'P%d' % cnt, line)
                        search_para = re.search(r'%s\_\d' % par, line)

                        cnt += 1

                    rules.add(line)
        print('select %d association rules' % len(rules))

        if save:
            joblib.dump(norm_rule_dict, "{}/data/norm_rule_dict.pkl".format(self.name))
            joblib.dump(rules, "{}/data/rules.pkl".format(self.name))

        return norm_rule_dict, rules

if __name__ == "__main__":

    data_dir = '.'
    protocol_name = 'mutualEx'
    processor = DataProcess(data_dir, protocol_name, replace_index=None)
    guard = processor.getguard('Idle')
    dataset, itemMeaning, para_digit = processor.exe_single(abs_type='NODE', guard=guard)
    print('dataset is {}'.format(dataset))
    global_vars = processor.select_global(itemMeaning)
    learner = RuleLearing(data_dir, protocol_name, dataset, itemMeaning, global_vars=global_vars, max_freq_size=3,
                          min_support=0.1, min_confidence=1.0)
    rule_tuple, rule_string_list = learner.execute()
    assert len(rule_tuple) == len(rule_string_list)
    all_types = {'NODE': 'NODENUMS'}
    instantiator = RuleLearing(data_dir, protocol_name, [], {})
    instan_rule_tuple, _ = instantiator.instantiate(rule_tuple, rule_string_list, all_types)
    home_flag=False
    prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir, protocol_name))
    print_info, candidate_inv_string = prot_analyzer.single_refine_abstract(instan_rule_tuple, abs_type='NODE',
                                                               guard=guard, print_usedinvs_to_file=False, boundary_K=1)
    print("print_info is {}:".format(print_info))
    candidate_inv_string = list(set(candidate_inv_string))
    candidate_inv_tuple = list(map(lambda x: split_string_to_tuple(x), candidate_inv_string))
    assert len(candidate_inv_string) == len(candidate_inv_tuple)
    print('select candidate association rules: before: {}, after: {}'.format(len(instan_rule_tuple),
                                                                             len(candidate_inv_tuple)))

