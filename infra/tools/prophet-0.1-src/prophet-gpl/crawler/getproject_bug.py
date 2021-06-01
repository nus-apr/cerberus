#GitHub project crawler
#Format:
#   python getproject.py projectname project_owner
#   i.e python getproject.py metalsmith segmentio
#

from pygithub3 import Github
import urllib
import json
import sys
import os
import io
import zipfile
import time

if __name__ == '__main__':
    project_name = sys.argv[1]
    user_name = sys.argv[2]
    print('Username = '+user_name )
    print('Project = '+project_name )
    
    gh = Github(user=user_name, repo=project_name,login='zichaoqi',password='1qaz@WSX');
    token = '?access_token=4fca22d76a306f11c5cedec029ab719ab4490ede';
    #token could be gained from
    #curl -u "zichaoqi" https://api.github.com/authorizations
    
    cm_list = gh.repos.commits.list().all()
    
    cur_dir = os.getcwd()
    pro_dir = os.path.join(cur_dir,project_name+'_'+user_name);
    if not os.path.isdir(pro_dir):
        os.makedirs(pro_dir);
        
    
    print('API Limit = '+str(gh.remaining_requests));
    
    print("#commit = "+str(len(cm_list)))
    mess_dir = os.path.join(pro_dir,'message.txt');
    f_mess = io.open(mess_dir,'a');
    
    #for i in xrange(0,len(cm_list)):
    for i in xrange(0,len(cm_list)):
        single_cm = cm_list[i];
        print('Debug_url = '+single_cm.url);
        
        res = urllib.urlopen(single_cm.url+token).read()
        info = json.loads(res);
        sha = info['sha']
        print('(' + str(i+1) +'/'+ str(len(cm_list)) + ')Get sha '+sha)
        
        
        commit_message = info['commit']['message'].lower();
        if not ('bug' in commit_message):
            continue;
        
        
        with io.open(os.path.join(pro_dir,sha+'.json'), 'w', encoding='utf-8') as f:
          f.write(unicode(json.dumps(info, ensure_ascii=False)))
        
        f_mess.write(sha+'\n')
        f_mess.write(info['commit']['message']+'\n');
        f_mess.flush()
        
        fileurl = 'https://github.com/'+user_name+'/'+project_name+'/'+'archive/'+sha+'.zip';
        os_url = os.path.join(pro_dir,sha+'.zip');
        
        print('Downloading file from '+fileurl);
        urllib.urlretrieve(fileurl, os_url )
        
        #print('Extracting '+os_url);
        #with zipfile.ZipFile(os_url, "r") as z:
        #    z.extractall(pro_dir)
        
        #os.remove(os_url);
        
        #time.sleep(1);#avoid exceeding rate limit of GitHub api v3
        
    f_mess.close()

