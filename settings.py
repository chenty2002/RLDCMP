#coding=utf-8

# maximum sleep time while there is no connect for a smv process
MAX_SLEEP_TIME = 5

# time out in seconds
TIME_OUT = 5
MU_CHECK_TIMEOUT = 12000
MU_CHECK_MEMORY = 4096

# path to murphi
MU_PATH = '/home/cmurphi5.5.0/src/mu'
MU_INCLUDE = '/home/cmurphi5.5.0/include'
GXX_PATH = '/usr/bin/g++'

# path for storing murphi files
MU_FILE_DIR = '/tmp/cmurphi'

dirs = [MU_FILE_DIR]

import os

for d in dirs:
    if not os.path.isdir(d):
        os.makedirs(d)
