from __future__ import print_function
from __future__ import unicode_literals
import os
from settings import MU_PATH, MU_INCLUDE
from abstract import initAbs, doMurphiCheck, learn_str, test_abs_str
from prompt_toolkit import prompt
from prompt_toolkit.history import FileHistory
from prompt_toolkit.auto_suggest import AutoSuggestFromHistory
from prompt_toolkit.completion import WordCompleter

def IRCMP(name, v_mode):
    data_dir = '.'
    protocol_name = name

    # 生成可达集文件
    if not os.path.exists('{1}/{0}/{0}.txt'.format(protocol_name, data_dir)):
        command1 = "{2} {0}/{1}/{1}.m".format(data_dir, protocol_name, MU_PATH)
        command2 = "g++ -ggdb -o {0}/{1}/{1}.o {0}/{1}/{1}.cpp -I {2} -lm".format(data_dir, protocol_name, MU_INCLUDE)
        command3 = "{0}/{1}/{1}.o -m 4096 -ta >{0}/{1}/{1}.txt".format(data_dir, protocol_name)
        os.system(command1)
        assert os.path.exists("{0}/{1}/{1}.cpp".format(data_dir, protocol_name))
        os.system(command2)
        assert os.path.exists("{0}/{1}/{1}.o".format(data_dir, protocol_name))
        os.system(command3)
        assert os.path.exists("{0}/{1}/{1}.txt".format(data_dir, protocol_name))

        os.remove("{0}/{1}/{1}.cpp".format(data_dir, protocol_name))
        os.remove("{0}/{1}/{1}.o".format(data_dir, protocol_name))

    #删除旧有的抽象协议
    if os.path.exists('./{0}/ABS{0}.m'.format(protocol_name)):
        os.remove('./{0}/ABS{0}.m'.format(protocol_name))

    # 生成新的抽象协议
    initAbs("./{0}/{0}.m".format(protocol_name), "./ABS{0}.m".format(protocol_name))

    if os.path.exists('./ABS{0}.m'.format(protocol_name)):
        with open('./ABS{0}.m'.format(protocol_name), 'r') as f:
            text = f.read()
            assert text != ''
    with open("{}/{}/str_{}.m".format(data_dir, protocol_name, protocol_name), 'w') as f:
        f.write(text)

    #删除已有的加强记录
    if os.path.exists("{}/{}/abs_process.csv".format(data_dir, protocol_name)):
        os.remove("{}/{}/abs_process.csv".format(data_dir, protocol_name))
    os.system('touch {}/{}/abs_process.csv'.format(data_dir, protocol_name))

    checked = []
    flag , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)

    inv_num = 1
    while flag != None:
        if v_mode == 'n':
            suc = learn_str(str(flag), name = protocol_name)
            if suc == -1:
                flag  , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)
                continue
        inv_num = test_abs_str(flag = flag, name = protocol_name,inv_num= inv_num)
        flag  , checked = doMurphiCheck('ABS{}'.format(protocol_name), checked)
        print(checked)
    print("success!")

    os.system('mv {0}/ABS{1}.m {0}/{1}/'.format(data_dir, protocol_name))


if __name__ == '__main__':
    print('='*37 +'IRCMP'+ '='*37)
    print('Welcome to IRCMP, this tool is going to help you to verify protocol.')
    print('1.Please make sure the Cmurphi has been installed, \n  and the config is right in settings.py.')
    print('2.We provide several testing protocols including:\n\tmesi | moesi | mutualEx | german | flash.')
    print('3.if you just want to verify a protocol simply with existing lemmas, \n  please select \'y\' in the second option. \n  Otherwise if you want to go through the full learning process, select \'n\'.')
    print('4.Input \'exit\' to exit the program.')
    print('='*79)

    protocol_list = ['mutualEx', 'german', 'mesi', 'moesi', 'flash']
    Prot_Completer = WordCompleter(protocol_list,  ignore_case=True)

    while True:
        user_input = prompt('Protocol Name > ', completer = Prot_Completer)
        print(user_input)
        if (user_input.strip().lower() == 'exit'):
            print('***INTERRUPTED***')
            exit(0)
        else:
            if user_input in protocol_list:
                v_mode = prompt('Verify Protocol Simply? (y/n) > ')
                if v_mode not in ('y', 'n'):
                    print('***Wrong Input***')
                elif v_mode.strip().lower() == 'exit':
                    print('***INTERRUPTED***')
                    exit(0)
                else:
                    IRCMP(user_input, v_mode)
            else:
                print('***Wrong Protocol Name***')