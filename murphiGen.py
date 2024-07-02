#-*- coding: UTF-8 -*- 
import os
import argparse
import time
import logging
from settings import MU_PATH, MU_INCLUDE
from abstract import initAbs, doMurphiCheck, learn_inv, abs_str, Replace

arg_parser = argparse.ArgumentParser(description='Learning based CMP')
arg_parser.add_argument('-t', '--task', help="Choice which protocol to be verified.", default='mutualEx')
arg_parser.add_argument('-s', '--simp', help="Only using existed invariants to verify the protocol.", type=str, choices=['y', 'n'], default='y')
args = arg_parser.parse_args()

dir_path = '.'
protocol_name = args.task

class MyLogging:
    def __init__(self, protocol):
        self.logPath = './{}/'.format(protocol)
        self.logName = '{}.log'.format(protocol)
        self.logFile = self.logPath + self.logName
        self.temptime = 0
        self.temp_num = 0
        self.pre_time = 0
        self.learn_time = 0
        self.filter_time = 0
        self.str_time = 0
        self.asso_num = 0
        self.inv_num = 0
        self.str_num = 0
        logging.basicConfig(
            level=logging.INFO,  # 级别：CRITICAL > ERROR > WARNING > INFO > DEBUG，默认级别为 WARNING
            format='%(asctime)s %(filename)s[line:%(lineno)d] %(levelname)s:  %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S',
            filename=self.logFile,
            filemode='a')

    def write_log(self, content):
        logging.info(content)

if os.path.exists('./{0}/{0}.log'.format(protocol_name)):
    os.remove('./{0}/{0}.log'.format(protocol_name))
my_log = MyLogging(protocol_name)

start_time = time.time()

gen_time = time.time()
# generate reachable states
if not os.path.exists('{1}/{0}/{0}_reach.txt'.format(protocol_name, dir_path)):
    gen_time = time.time()
    command1 = "{2} {0}/{1}/{1}.m".format(dir_path, protocol_name, MU_PATH)
    command2 = "g++ -ggdb -o {0}/{1}/{1}.o {0}/{1}/{1}.cpp -I {2} -lm".format(dir_path, protocol_name, MU_INCLUDE)
    command3 = "{0}/{1}/{1}.o -m 4096 -ta >{0}/{1}/{1}_reach.txt".format(dir_path, protocol_name)
    os.system(command1)
    assert os.path.exists("{0}/{1}/{1}.cpp".format(dir_path, protocol_name))
    os.system(command2)
    assert os.path.exists("{0}/{1}/{1}.o".format(dir_path, protocol_name))
    os.system(command3)
    assert os.path.exists("{0}/{1}/{1}_reach.txt".format(dir_path, protocol_name))

    os.remove("{0}/{1}/{1}.cpp".format(dir_path, protocol_name))
    os.remove("{0}/{1}/{1}.o".format(dir_path, protocol_name))
    gen_time_2 = time.time()
    print('The time to generate the reachable states is: {}'.format(str(gen_time_2-gen_time)))

# delete existed protocol file
if os.path.exists('./{0}/ABS{0}.m'.format(protocol_name)):
    os.remove('./{0}/ABS{0}.m'.format(protocol_name))

# generate new abstracted protocol 
initAbs("./{0}/{0}.m".format(protocol_name), "./ABS{0}.m".format(protocol_name))

if os.path.exists('./ABS{0}.m'.format(protocol_name)):
    with open('./ABS{0}.m'.format(protocol_name), 'r') as f:
        text = f.read()
        assert text != ''
with open("{}/{}/str_{}.m".format(dir_path, protocol_name, protocol_name), 'w') as f:
    f.write(text)

# delete existed strengthen info
if os.path.exists("{}/{}/abs_process.csv".format(dir_path, protocol_name)):
    os.remove("{}/{}/abs_process.csv".format(dir_path, protocol_name))
os.system('touch {}/{}/abs_process.csv'.format(dir_path, protocol_name))

gen_time_2 = time.time()
my_log.write_log(content='Time spent in preparation is: {} \n\n'.format(str(gen_time_2-gen_time)))

checked = []
flag , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)

inv_num = 0
rep = Replace(dir_path, protocol_name)
while flag != None:
    if args.simp == 'n':
        suc = learn_inv(str(flag), name = protocol_name, rep = rep, log = my_log)
        if suc == -1 :
            flag  , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)
            continue
    my_log.str_num += 1
    inv_num = abs_str(flag = flag, name = protocol_name,inv_num = inv_num,rep =rep, log = my_log)
    flag  , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)
    print(checked)

os.system('mv {0}/ABS{1}.m {0}/{1}/'.format(dir_path, protocol_name))

rep.replace()
rep.save()

print("success!")

end_time = time.time()
print("Total time spent : {}".format(str(end_time - start_time)))
my_log.write_log(content="success! Total spent time : {0}; Learn: {1}; Select: {2}; Strengthen: {3} \n\n".format(str(end_time - start_time), str(my_log.learn_time), str(my_log.filter_time), str(my_log.str_time)))
my_log.write_log(content="len of assoRules : {0}; len of auxInvs : {1}; the number of strengthened rules : {2}".format(my_log.asso_num, my_log.inv_num, my_log.str_num))
