# Add html 'id' attributes to all the headers of the html pages
# passed as argument that do not already have one.

import sys
import glob

from bs4 import BeautifulSoup


def pygments_file(pathname):
    with open(pathname, "r") as f:
        print(f"Treating {pathname}")
        html_doc = f.read()

    soup = BeautifulSoup(html_doc, features="html.parser")

    # Add an id to each main header if needed
    for H in "h1", "h2", "h3", "h4", "h5", "h6":
        index = 0
        for h in soup.find_all(H):
            if not h.get("id"):
                h["id"] = f"{H}.{index}"
                index += 1

    if soup.body:
        with open(pathname, "wb") as f:
            f.write(soup.encode_contents())


if len(sys.argv) > 1:
    p = str(sys.argv[1])
else:
    print(f"Usage: {sys.argv[0]} <glob>")
    exit(1)

pathnames = glob.glob(p)
for pathname in pathnames:
    pygments_file(pathname)
