import subprocess


def list_submodules():
    p = subprocess.check_output(
        ["git", "config", "--file", ".gitmodules", "--get-regexp", "path"],
    )
    return [item.split(".")[1] for item in p.decode("utf-8").splitlines()]


def list_staged_files():
    p = subprocess.check_output(
        ["git", "diff", "--name-only", "--cached"],
    )
    return p.decode("utf-8").splitlines()


if __name__ == "__main__":
    staged_files = list_staged_files()
    for m in list_submodules():
        if m in staged_files:
            print(f"submodule {m} is staged for commit")
            exit(1)
