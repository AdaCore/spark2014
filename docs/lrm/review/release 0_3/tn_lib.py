#!/usr/bin/env python

""" A library for manipulating review tokens.

    This is mainly used in the commit hook to check if a review token is
    well formed, so be careful if you change it as it may break the hook.
"""

import re

# The right order for the headers (useful for formatting tools)
HEADER_ORDER = [
   "implementer",
   "reviewer",
   "revision_reviewed",
   "description",
   "flag_release_note",
   "flag_user_docs",
   "flag_test_case",
   "flag_test_diffs",
   "flag_proof",
   "affected_courses",
   "affected_tools",
   "flag_addresses_ticket",
   "review_completed",
   "flag_devlog",
   "flag_branch_deleted",
   "flag_dead",
   ]

# Used to map the long desciptive header to the short key used in all
# scripts and future supporting applications
HEADER_REGEX_MAP = {
   "implementer": "implementer",
   "reviewer": "reviewer",
   "revision.*reviewed": "revision_reviewed",
   "description": "description",
   "release note": "flag_release_note",
   "user docs": "flag_user_docs",
   "test case": "flag_test_case",
   "test diffs": "flag_test_diffs",
   "proof of changes": "flag_proof",
   "courses affected": "affected_courses",
   "all issues.*addressed": "flag_addresses_ticket",
   "tools affected": "affected_tools",
   "review completed": "review_completed",
   "devlog updated": "flag_devlog",
   "branch.*deleted": "flag_branch_deleted",
   "tn marked dead": "flag_dead",
   }

# Describes which field can take what data
HEADER_FIELDS = {
   "implementer": {
      "name": "Implementer",
      "type": "text",
      },
   "reviewer": {
      "name": "Reviewer",
      "type": "text",
      },
   "revision_reviewed": {
      "name": "Revision reviewed",
      "type": "revision",
      },
   "description": {
      "name": "TN Description",
      "type": "text",
      },
   "flag_release_note": {
      "name": "Release Note Updated",
      "type": "bool",
      },
   "flag_user_docs": {
      "name": "User Docs Updated",
      "type": "bool",
      },
   "flag_test_case": {
      "name": "Test Case Added",
      "type": "bool",
      },
   "flag_test_diffs": {
      "name": "Test diffs checked and updated",
      "type": "bool",
      },
   "flag_proof": {
      "name": "RTE proof of changes done",
      "type": "bool",
      },
   "affected_courses": {
      "name": ("Courses affected? "
               "(SWEWS, ASPDV, UML, RavenSPARK, Checker)"),
      "type": "text",
      },
   "affected_tools": {
      "name": ("Other tools affected? "
               "(eg POGS, SPARKMake, SPARKFormat, UML Profile, GPS)"),
      "type": "text",
      },
   "flag_addresses_ticket": {
      "name": "Check messages under this TN - Are all issues addressed?",
      "type": "bool",
      },
   "review_completed": {
      "name": "Review completed",
      "type": "initials+revision",
      },
   "flag_devlog": {
      "name": "AdaCore DevLog updated",
      "type": "bool",
      },
   "flag_branch_deleted": {
      "name": "Check that branch has been deleted or never existed",
      "type": "bool",
      },
   "flag_dead": {
      "name": "TN marked dead",
      "type": "bool",
      },
   }

# A sanity check in case this library changes
for x in set(HEADER_REGEX_MAP.values()) - set(HEADER_FIELDS.keys()):
   print "Syntax error: HEADER_FIELDS is missing an entry for %s" % x
for x in set(HEADER_FIELDS.keys()) - set(HEADER_REGEX_MAP.values()):
   print "Syntax error: HEADER_REGEX_MAP is missing an entry for %s" % x
for x in set(HEADER_ORDER) - set(HEADER_FIELDS.keys()):
   print "Syntax error: HEADER_ORDER is missing an entry for %s" % x
for x in set(HEADER_FIELDS.keys()) - set(HEADER_ORDER):
   print "Syntax error: HEADER_ORDER has spurious entry %s" % x
assert (set(HEADER_REGEX_MAP.values()) == set(HEADER_FIELDS.keys()))

# All fields required for each commment
REQUIRED_FIELDS = frozenset(["location", "description", "action taken",
                             "checked by", "label"])

def find_header_key(full_text_header):
   """ Maps the long header to the short key used internally in the GUI """
   for r in HEADER_REGEX_MAP:
      if re.search(r, full_text_header.lower()):
         return HEADER_REGEX_MAP[r]
   return None

def parse_tn(filename, tn_text):
   """ This function reads a given review token and returns a dictionary
       of the following format:
          ticket -- the guessed TN based on the file name
          header -- a dictionary of each flag
          comments -- a list containing a dictionary for each comment
                      raised
          errors -- a list containing any errors found during parsing
       The format of the comment dictionaries is as follows:
          location
          description
          action taken
          checked by
   """
   rv = {
      "header": {},
      "comments": [],
      "ticket": filename.rsplit(".", 1)[0],
      "errors": [],
      }

   # Split into header and content section
   try:
      # The slightly tedious form is to handle dodgy line-endings
      header, content = "\n".join(tn_text.splitlines()).split("\n\n", 1)
   except ValueError:
      rv["errors"].append("Malformed file: Could not split into header "
                          "and content sections.")
      return rv

   # Parse header
   for l in header.splitlines():
      # Sanity check syntax
      if not l.startswith("!") and ":" in l:
         rv["errors"].append("Malformed header: '%s'" % l)
         continue

      # Split into key and value
      try:
         k, v = [x.strip() for x in l[1:].split(":", 1)]
      except ValueError:
         rv["errors"].append("Malformed file: Could not parse header '%s'" % l)
         return rv
      key = find_header_key(k)
      if key:
         if key not in rv["header"]:
            rv["header"][key] = v
         else:
            rv["errors"].append("Duplicate header: '%s'" % k)
      else:
         rv["errors"].append("Unknown header: '%s'" % k)

   # Check that all headers are present
   for h in HEADER_FIELDS:
      if h not in rv["header"]:
         rv["errors"].append("Missing header: '%s'" % HEADER_FIELDS[h]["name"])
         rv["header"][h] = ""

   # Parse comments
   cc = {}
   current_key = None
   for l in content.splitlines():
      lcl = l.lower()
      if (lcl.startswith("!location:") or lcl.startswith("!description:") or
          lcl.startswith("!action taken:") or lcl.startswith("!checked by:") or
          lcl.startswith("!label:")):
         current_key = l.split(":", 1)[0][1:].lower()
         # We've already seen that key for this comment, so it must be
         # a new comment
         if current_key in cc:
            for x in cc:
               cc[x] = cc[x].rstrip()
            rv["comments"].append(cc)
            cc = {}
         cc[current_key] = l.split(":", 1)[1].strip()
      elif current_key:
         cc[current_key] += ("\n" + l.rstrip())
   # Deal with dangling comments
   if len(cc):
      for x in cc:
         cc[x] = cc[x].rstrip()
      rv["comments"].append(cc)

   #
   # Parsing is done. Some extra checks follow.
   #

   # Check that each comment has all fields specified and insert blank ones
   # for missing fields
   for comment_number, comment in enumerate(rv["comments"]):
      unknown_fields = set(comment.keys()) - REQUIRED_FIELDS
      missing_fields = REQUIRED_FIELDS - set(comment.keys())
      if len(unknown_fields):
         rv["errors"].append("Comment %u has the following unknown fields: %s" %
                             (comment_number + 1, ", ".join(unknown_fields)))
      for f in missing_fields:
         rv["errors"].append("Comment %u is missing the required field `%s'" %
                             (comment_number + 1, f))
         comment[f] = ""

   # Check and update types where applicable
   for k, v in rv["header"].iteritems():
      required_type = HEADER_FIELDS[k]["type"]
      # Blank values are always OK at this stage
      if v == "":
         rv["header"][k] = None
         continue

      # Check contents
      if required_type == "bool":
         if v.lower() not in set(["y", "n", "yes", "no"]):
            rv["errors"].append("Bad value '%s' for header '%s'. "
                                "Should be yes, no or blank." % (v, k))
         else:
            rv["header"][k] = v.lower().startswith("y")
      elif required_type == "revision":
         tmp = re.match("^r? ?([0-9]+)$", v)
         if not tmp:
            rv["errors"].append("Bad value '%s' for header '%s'. "
                                "Should be a revision or blank." % (v, k))
         else:
            rv["header"][k] = int(tmp.group(1))
      elif required_type == "initials+revision":
         tmp = re.match("^([A-Z]+),? ?r? ?([0-9]+)$", v)
         if not tmp:
            rv["errors"].append("Bad value '%s' for header '%s'. "
                                "Should be 'initials, revision' or blank."
                                % (v, k))
         else:
            rv["header"][k] = (tmp.group(1), int(tmp.group(2)))

   # If review is signed off, all comments must be as well
   if rv["header"]["review_completed"]:
      for i, comment in enumerate(rv["comments"]):
         if not comment["checked by"]:
            rv["errors"].append("Review is signed off despite "
                                "comment %u which isn't." % (i+1))

   # If ticket is marked dead:
   # - review must be signed off
   # - branch must be deleted
   if rv["header"]["flag_dead"]:
      if not rv["header"]["review_completed"]:
         rv["errors"].append("Ticket is marked dead despite "
                             "review not being signed off.")
      if not rv["header"]["flag_branch_deleted"]:
         rv["errors"].append("Ticket is marked dead but you "
                             "still need to check that either "
                             "no branch ever existed or that "
                             "it has been deleted.")

   return rv

def write_tn(tn):
   FORMATS = {
      "bool": (lambda x: {True: "y", False: "n", None: ""}[x]),
      "text": (lambda x: "" if x is None else str(x)),
      "revision": (lambda x: "" if x is None else "r%u" % x),
      "initials+revision": (lambda x: "" if x is None else "%s, r%u" % x)
      }

   COMMENT_FIELD_ORDER = ("Label", "Location", "Description",
                          "Action Taken", "Checked By")

   rv = "\n".join(("!%s: %s"
                   % (HEADER_FIELDS[h]["name"],
                      FORMATS[HEADER_FIELDS[h]["type"]]\
                         (tn["header"].get(h, None)))).rstrip()
                  for h in HEADER_ORDER) + "\n"

   rv += "\n"

   rv += "\n\n".join("\n".join(("!%s: %s" % (cf, comment[cf.lower()])).rstrip()
                               for cf in COMMENT_FIELD_ORDER)
                     for comment in tn["comments"]) + "\n"

   return rv
