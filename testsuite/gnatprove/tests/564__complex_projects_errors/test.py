from test_support import prove_all

print("###########")
print("analyze Prj")
print("###########")
prove_all(project="prj.gpr")

print("############")
print("analyze Prj2")
print("############")
prove_all(project="prj2.gpr")
