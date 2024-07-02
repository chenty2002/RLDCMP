import re
import os
import sys
import subprocess
from settings import MU_PATH, MU_INCLUDE
from process import to_murphi
import multiprocessing

def multi_callmurphi(filter_file, string_list, data_dir, protocol_name, all_types):
    remove_list = []
    str_len = len(string_list)
    core_num = str_len//100 + 1
    cnt = 0
    rng = []
    while(cnt < str_len):
        with open('{}/{}/tempfile_{}.m'.format(data_dir, protocol_name, cnt), 'w') as f:
            f.write(filter_file+'\n')
            for i in range(cnt, min(cnt+100, str_len)):
                inv_name = 'auxinv_%d'%i
                inv = to_murphi(inv_name, string_list[i], all_types)
                f.write(inv[0]+'\n')
            rng.append(cnt)
            cnt = min(cnt+100, str_len)
    with multiprocessing.Pool(core_num) as p:
        remove_list.extend(p.starmap(run_murphi, [(c, data_dir, protocol_name) for c in rng])) 
    remove_list = list(set(k for key in remove_list for k in key))
    
    return remove_list


def run_murphi(cnt, data_dir, prot_name, aux_para=''):
    print('[call murphi]compile murphi to cpp....')
    command1 = "./cmurphi5.5.0-v1_hid/src/mu {1}/{0}/tempfile_{2}.m".format(prot_name, data_dir, cnt)
    command2 = "g++ -ggdb -o {0}/{1}/tempfile_{2}.o {0}/{1}/tempfile_{2}.cpp -I ./cmurphi5.5.0-v1_hid/include -lm".format(data_dir, prot_name, cnt)
    command3 = "{0}/{1}/tempfile_{3}.o -m 4096 {2}".format(data_dir, prot_name, aux_para, cnt)

    print('command1 = {}'.format(command1))
    print('command2 = {}'.format(command2))
    print('command3 = {}'.format(command3))

    print('compile murphi file to cpp....')

    process1 = subprocess.Popen(command1,
                                shell=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    (stdout, stderr) = process1.communicate()
    if not re.search(r'Code generated', stdout.decode('utf-8')):
        print('Wrong', stderr.decode('utf-8'))
        raise ValueError
        sys.exit()
    else:
        print('Code generated')

    print('compile .cpp to .o file....')
    try:
        process2 = subprocess.Popen(command2, shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        (stdout, stderr) = process2.communicate()
    except:
        raise ValueError(stdout.decode('utf-8'))

    print('running .o file....')

    try:
        process = subprocess.Popen(command3, shell=True,
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)

        (stdoutdata, stderrdata) = process.communicate()
    except:
        raise ValueError(stdout.decode('utf-8'))
    else:
        if re.findall('Too many active states', stdoutdata.decode('utf-8')):
            raise ValueError('Too many active states')
        # pattern_counter = re.compile(r'Invariant\s"auxinv_(\w+).*"\sfailed.')
        pattern_counter = re.compile(r'auxinv_(\w+)')
        counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))
    
    print('counter_ex is {}'.format(counter_ex))
    os.remove('{0}/{1}/tempfile_{2}.m'.format(data_dir, prot_name, cnt))
    os.remove('{0}/{1}/tempfile_{2}.cpp'.format(data_dir, prot_name, cnt))
    os.remove('{0}/{1}/tempfile_{2}.o'.format(data_dir, prot_name, cnt))

    return counter_ex if len(counter_ex) else []

if __name__ == "__main__":
    data_dir = '.'
    protocol_name = 'mutualEx'
    command1 = "{2} {0}/{1}/{1}.m".format(data_dir, protocol_name, MU_PATH)
    command2 = "g++ -ggdb -o {0}/{1}/{1}.o {0}/{1}/{1}.cpp -I {2} -lm".format(data_dir, protocol_name, MU_INCLUDE)
    command3 = "{0}/{1}/{1}.o -m 4096 -ta >{0}/{1}.txt".format(data_dir, protocol_name)
    os.system(command1)
    assert os.path.exists("{0}/{1}/{1}.cpp".format(data_dir, protocol_name))
    os.system(command2)
    assert os.path.exists("{0}/{1}/{1}.o".format(data_dir, protocol_name))
    os.system(command3)
    assert os.path.exists("{0}/{1}.txt".format(data_dir, protocol_name))