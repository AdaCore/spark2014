import re
import subprocess

from docutils import nodes

# This extension massages the HTML output of Sphinx, so that the pagefind
# binary can create a searchable index. It should only be loaded if pagefind is
# in the path.


def slugify(text):
    """Convert text to a slug format, making it suitable for use as an HTML id."""
    # Remove non-alphanumeric characters and replace spaces with hyphens
    text = re.sub(r"[^a-zA-Z0-9 ]", "", text)
    return text.strip().lower().replace(" ", "-")


# Add ids tags to all the titles in the documents. This is needed
# by Pagefind itself, in order to be able refer to headers.
def add_custom_ids(app, doctree, docname):
    for section in doctree.traverse(nodes.section):
        title_node = section.next_node(nodes.title)

        if title_node is not None:
            # Slugify the title text
            section_title = slugify(title_node.astext())

            # Generate the unique id by combining the slugified title and the
            # line number
            unique_id = f"{section_title}-l{section.line}"

            # Apply id to the section and title nodes
            if unique_id not in section["ids"]:
                section["ids"].append(unique_id)
            if unique_id not in title_node["ids"]:
                title_node["ids"].append(unique_id)


def run_pagefind(app, exception):
    # Only run if there were no errors during the build, and if the html
    # documentation has actually been ran
    if exception is None and app.builder.name == "html":
        subprocess.run(["pagefind", "--verbose"])


def setup(app):
    app.connect("doctree-resolved", add_custom_ids)
    app.connect("build-finished", run_pagefind)
