from e3.auth.gitlab import gen_gitlab_token
import gitlab

token = gen_gitlab_token()
gl = gitlab.Gitlab("https://gitlab.adacore-it.com", private_token=token["token"])

spark_project_id = 168

spark_project = gl.projects.get(spark_project_id)

issues = spark_project.issues.list(state="opened", iterator=True)

# issues is an iterator that gets consumed when iterating, copying it to a
# standard list
issues = [x for x in issues]

counts = {}
for issue in issues:
    for label in issue.labels:
        if label not in counts:
            counts[label] = 0
        counts[label] += 1

output = [(k, v) for k, v in counts.items()]
output.sort(key=lambda x: x[0])

for k, v in output:
    print(f"{k} : {v}")
print(f"Total: {len(issues)}")
