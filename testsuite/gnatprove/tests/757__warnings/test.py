from test_support import prove_all


print("---- expect warning related to recursion -------")
prove_all()
# detection of incorrect warning name
print("---- expect error for unknown warning name -------")
prove_all(opt=["-W", "variant-no-recursiop"])

# suppression of warning
print("---- no warning related recursion -------")
prove_all(opt=["-A", "variant-no-recursion"])

# promoting warning to error
print("---- expect error instead of warning -------")
prove_all(opt=["-D", "variant-no-recursion"])

# command-line behavior (override)
print("---- expect no warning -------")
prove_all(opt=["-D", "variant-no-recursion", "-A", "variant-no-recursion"])

# enabling of warning
print("---- expect warning for image attribute -------")
prove_all(opt=["-W", "image-attribute-length", "-A", "variant-no-recursion"])

# file-specific switches behavior
print("---- expect warning for image attribute, with tag -------")
prove_all(
    opt=[
        "-P",
        "test2.gpr",
        "-A",
        "variant-no-recursion",
    ]
)
