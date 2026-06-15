"""GitLab utilities shared by testsuite maintenance scripts."""

import os
import re
import tempfile
import time
import zipfile
from dataclasses import dataclass
from typing import Literal

import gitlab
from e3.auth.gitlab import GitlabRegistry

SPARK2014_GITLAB_ID = "168"


@dataclass
class GitLabProjectDescription:
    id: str
    """GitLab project Id."""

    artifact_regexps: list[str]
    """
    Job names for the project's pipelines that contain the relevant artifacts.
    """


@dataclass
class MRPipelineLookup:
    status: Literal["pipeline", "invalid_mr", "excluded"]
    pipeline_id: str | None = None
    reason: str | None = None


class NoSuchPipeline(Exception):
    """Raised when the pipeline was not found in the GitLab project."""

    pass


def make_gitlab_client():
    """Return an authenticated python-gitlab client."""
    proxy_url = os.environ.get("GITLAB_PROXY_URL")
    if proxy_url:
        return gitlab.Gitlab(proxy_url, keep_base_url=True)

    return gitlab.Gitlab(
        f"https://{GitlabRegistry.GITLAB_DOMAIN}",
        private_token=GitlabRegistry().token,
    )


def _project(gl, project_id):
    return gl.projects.get(project_id, lazy=True)


def get_pipeline_from_mr(gl, project_id, mr_id):
    """Resolve an MR id to a finished pipeline.

    Returns an ``MRPipelineLookup`` with one of these outcomes:
    - ``pipeline``: found a finished pipeline and returns its id;
    - ``invalid_mr``: MR id is not valid (caller may fallback to pipeline id);
    - ``excluded``: MR exists but is not eligible (caller should stop).
    """
    project = _project(gl, project_id)
    try:
        mr = project.mergerequests.get(mr_id)
    except gitlab.GitlabGetError as exc:
        if exc.response_code == 404:
            return MRPipelineLookup(status="invalid_mr", reason="MR not found")
        raise

    if mr is None:
        return MRPipelineLookup(
            status="invalid_mr",
            reason="unexpected MR API response",
        )

    if mr.state == "closed":
        return MRPipelineLookup(status="excluded", reason="MR is closed")

    finished_statuses = {"success", "failed", "canceled"}
    for pipeline in mr.pipelines.list(iterator=True):
        if pipeline.status in finished_statuses:
            return MRPipelineLookup(status="pipeline", pipeline_id=str(pipeline.id))

    return MRPipelineLookup(status="excluded", reason="MR has no finished pipeline")


def resolve_pipeline_id(gl, project_id, mr_or_pipeline_id):
    """Resolve an MR or pipeline id string to a pipeline id.

    If the id matches an MR, return the most recent finished pipeline for that
    MR.  If it does not match any MR, treat it as a direct pipeline id.
    Print a message and exit if the MR exists but has no suitable pipeline.
    """
    lookup = get_pipeline_from_mr(gl, project_id, mr_or_pipeline_id)
    if lookup.status == "pipeline":
        assert lookup.pipeline_id is not None
        print(f"MR {mr_or_pipeline_id}: using pipeline {lookup.pipeline_id}")
        return lookup.pipeline_id
    elif lookup.status == "invalid_mr":
        return mr_or_pipeline_id
    else:
        reason = lookup.reason or "MR excluded"
        print(f"MR {mr_or_pipeline_id} doesn't have a suitable pipeline: {reason}")
        raise SystemExit(1)


def find_job_in_pipeline(gl, project_id, pipeline_id, job_name):
    """Return the job id for job_name in the given pipeline, or None."""
    project = _project(gl, project_id)
    pipeline = project.pipelines.get(pipeline_id)
    for job in pipeline.jobs.list(iterator=True, include_retried=True):
        if job.name == job_name:
            return job.id
    return None


def download_job_artifact(gl, project_id, job_id, artifact_path):
    """Download artifact_path from a job and return the path to a temp file."""
    project = _project(gl, project_id)
    artifact = project.jobs.get(job_id).artifact(artifact_path)
    suffix = os.path.splitext(artifact_path)[1]
    with tempfile.NamedTemporaryFile("wb", suffix=suffix, delete=False) as f:
        f.write(artifact)
        return f.name


def _download_artifact_archive(project, job):
    """Download a job artifact archive and return the path to a temp file."""
    print(f"Getting artifacts for job {job.id} ({job.name})...", end="", flush=True)
    try:
        artifact = project.jobs.get(job.id).artifacts()
    except gitlab.GitlabGetError as exc:
        if exc.response_code == 404:
            print("  no artifact found")
            return None
        raise

    with tempfile.NamedTemporaryFile("wb", suffix=".zip", delete=False) as f:
        f.write(artifact)
        print("  done")
        return f.name


def download_test_results(gl, project_desc, pipeline_id):
    """Download testsuite result directories from matching job artifacts."""
    result = []
    project = _project(gl, project_desc.id)

    print(f"Getting jobs for pipeline {pipeline_id}...", end="", flush=True)
    try:
        pipeline = project.pipelines.get(pipeline_id)
    except gitlab.GitlabGetError as exc:
        if exc.response_code == 404:
            print(f"  not found in project {project_desc.id}")
            raise NoSuchPipeline from exc
        raise
    print("  done")

    regexps = [re.compile(r) for r in project_desc.artifact_regexps]
    found = False
    for job in pipeline.jobs.list(iterator=True, include_retried=True):
        if not any(re.match(r, job.name) for r in regexps):
            continue

        if not getattr(job, "artifacts_file", None):
            print(f"Job {job.id} ({job.name}) has no archive artifact")
            continue

        artifact = _download_artifact_archive(project, job)
        if artifact is None:
            # this case is already printed about in download_artifact,
            # no need to print here.
            continue

        found = True
        targetdir = os.path.splitext(artifact)[0]
        with zipfile.ZipFile(artifact, "r") as zip_ref:
            zip_ref.extractall(targetdir)
        os.remove(artifact)

        for entry in os.listdir(targetdir):
            sub = os.path.join(targetdir, entry)
            if os.path.isdir(sub):
                result.append(sub)

    if not found:
        print("  no suitable artifact found")
    return result


def trigger_pipeline(gl, project_id, ref, variables=None):
    """Trigger a pipeline on ref and return (pipeline_id, web_url).

    variables, if provided, is a dict of variable names to string values.
    """
    project = _project(gl, project_id)
    data = {"ref": ref}
    if variables:
        data["variables"] = [{"key": k, "value": v} for k, v in variables.items()]
    pipeline = project.pipelines.create(data)
    return pipeline.id, getattr(pipeline, "web_url", "")


_TERMINAL_STATUSES = {"success", "failed", "canceled", "skipped"}


def wait_for_pipeline(gl, project_id, pipeline_id, poll_interval=30):
    """Poll pipeline until it reaches a terminal status.

    Prints a status line each poll cycle and returns the final status string.
    """
    project = _project(gl, project_id)
    while True:
        pipeline = project.pipelines.get(pipeline_id)
        status = getattr(pipeline, "status", "unknown")
        print(f"  pipeline {pipeline_id}: {status}")
        if status in _TERMINAL_STATUSES:
            return status
        time.sleep(poll_interval)
