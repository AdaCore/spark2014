from subprocess import check_output

from test_support import prove_all

# Standard'Target_Name must have the same value in GNATprove as in the
# compiler, which is machine-dependent, so generate the checked value here.

target = check_output(["gcc", "-dumpmachine"], encoding="utf-8").strip()
# Ada string literals use double quotes, so build the literal separately
# instead of quoting inside the f-string.
target_literal = '"' + target + '"'

with open("target_name.ads", "w") as f:
    f.write(
        f"""package Target_Name with SPARK_Mode is
   pragma Assert (Standard'Target_Name = {target_literal});
   pragma Assert (Standard'Target_Name = "spark");  --  @ASSERT:FAIL
end Target_Name;
"""
    )

prove_all()
