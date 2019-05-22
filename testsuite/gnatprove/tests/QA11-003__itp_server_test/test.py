from test_support import *
import time
import json

"""TO UPDATE: When this test needs updating, the problem is most likely that
the number in CST_NODE, CST_SPLIT and CST_GOAL are no longer relevant. To
change them, you need to modify itp_lib.py in GPS spark plugin and change the
debug variable to True (this make node number appear in manual proof). Then,
launch this test prove_all and then click edit manual proof. You just need to
report the ID number of the node above the split transformation in CST_NODE,
the node for split on CST_SPLIT and the node that is unproved (last one of the
tree) on CST_GOAL.
Note that you need to update the *.in file too with the CST_GOAL everywhere.
"""


""" This tests is a commandline test for the itp server. It launches a server as
a background process, and then pass it request in JSON. The output to be checked
are notifications written in JSON"""

DEAD = "Dead"
INITIALIZED = "Initialized"
NEXT_UNPROVEN = "Next_Unproven_Node_Id"
NOTIFICATION = "notification"
NODE_CHANGE = "Node_change"
NODE_ID = "node_ID"
PARENT_ID = "parent_ID"
LTASK = "task"
UTASK = "Task"
UMESSAGE = "Message"
LMESSAGE = "message"
NEW_NODE = "New_node"
LMESSAGE = "message"
MESS_NOTIF = "mess_notif"
RLIMIT = "\nrlimit: Real time limit (8 s) exceeded\n"
TASK_MONITOR = "Task_Monitor"

# Node above the split transformation
CST_NODE = 10
# Node corresponding to the split transformation
CST_SPLIT = 11
# Goal on which we apply z3 etc
CST_GOAL = 18

# This launches the itp_server
def launch_server(limit_line, input_file):

    installdir = spark_install_path()
    bindir = os.path.join(installdir, 'libexec', 'spark', 'bin')

    cmd = [os.path.join (bindir, "gnat_server"), "--limit-line", limit_line, "test.mlw"]
    # Create a pipe to give request to the process one by one.
    read, write = os.pipe()
    # process writes output to file, so we can avoid deadlocking
    with open ("proc.out", "w") as outfile:
        process = Run (cmd, cwd="gnatprove", input=read, output=outfile, bg=True, timeout=8)
        with open (input_file, "r") as in_file:
            for l in in_file:
                print(l)
                os.write(write, l)
                sleep(1)
        # Give the gnat_server time to end by itself. Thats why we send the
        # exit request
        process.wait()
    # read in the process output via the tempfile
    with open ("proc.out", "r") as infile:
        s = infile.read()
    s = re.sub('"pr_time" : ([0-9]*[.])?[0-9]+', '"pr_time" : "Not displayed"', s)
    # Parse the json outputs:
    l = s.split (">>>>")
    nb_unparsed = 0
    task_monitor = 0
    next_unproven = 0
    node_change = 0
    children_CST_NODE = 0
    children_CST_SPLIT = 0
    children = 0
    for i in l:
        try:
            pos = i.find("{")
            j = json.loads(i[pos:])
            notif_type = j[NOTIFICATION]
            if notif_type == NODE_CHANGE:
                node_change = node_change + 1
            elif notif_type == NEW_NODE:
                children = children + 1
                if j[PARENT_ID] == CST_SPLIT:
                    children_CST_NODE = children_CST_NODE + 1
                elif j[PARENT_ID] == CST_GOAL:
                    children_CST_SPLIT = children_CST_SPLIT + 1
            elif notif_type == NEXT_UNPROVEN:
                # TODO this is ok but we print nothing
                next_unproven = next_unproven + 1
            elif notif_type == INITIALIZED:
                print (INITIALIZED)
            elif notif_type == DEAD:
                print (DEAD)
            elif notif_type == UTASK:
                print (notif_type)
                print (j[LTASK])
            elif notif_type == UMESSAGE:
                message = j[LMESSAGE]
                message_type = message[MESS_NOTIF]
                if message_type == TASK_MONITOR:
                    task_monitor = task_monitor + 1
                    # TODO ignore task_monitoring
                else:
                    print (UMESSAGE)
            else:
                print ("TODO PROBLEM TO REPORT")
        except:
            if i == RLIMIT:
                print ("Process Ended")
            elif i != "\n" and i != " ":
                nb_unparsed = nb_unparsed + 1
                print ("UNPARSED NOTIFICATION " + i)
    if children_CST_NODE == 1:
        print ("Children CST_NODE OK")
    if children_CST_SPLIT == 3:
        print ("Children CST_SPLIT OK")
    if children == 5:
        print ("Children OK")
    print ("Unparsed JSON = " + str(nb_unparsed))
    print ("Next_unproven = " + str(next_unproven))
    print ("Node_change = " +  str(node_change))
    return "DONE"

prove_all(counterexample=False, prover=["cvc4"], cache_allowed=False)
sleep(5)
result = launch_server(limit_line="test.adb:11:16:VC_POSTCONDITION", input_file="test.in")
print (result)
