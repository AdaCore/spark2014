"""GitLab utilities shared by testsuite maintenance scripts."""

import os
import requests
import tempfile
import time
from dataclasses import dataclass
from typing import Literal

SPARK2014_GITLAB_ID = "168"


@dataclass
class MRPipelineLookup:
    status: Literal["pipeline", "invalid_mr", "excluded"]
    pipeline_id: str | None = None
    reason: str | None = None


def get_pipeline_from_mr(gl, project_id, mr_id):
    """Resolve an MR id to a finished pipeline.

    Returns an ``MRPipelineLookup`` with one of these outcomes:
    - ``pipeline``: found a finished pipeline and returns its id;
    - ``invalid_mr``: MR id is not valid (caller may fallback to pipeline id);
    - ``excluded``: MR exists but is not eligible (caller should stop).
    """
    mr_url = gl.base_url + f"/projects/{project_id}/merge_requests/{mr_id}"
    mr_response = requests.get(mr_url, gl.data)
    if mr_response.status_code == 404:
        return MRPipelineLookup(status="invalid_mr", reason="MR not found")

    mr = mr_response.json()
    if not isinstance(mr, dict):
        return MRPipelineLookup(
            status="invalid_mr",
            reason="unexpected MR API response",
        )

    if mr.get("state") == "closed":
        return MRPipelineLookup(status="excluded", reason="MR is closed")

    pipelines_url = (
        gl.base_url + f"/projects/{project_id}/merge_requests/{mr_id}/pipelines"
    )
    pipelines = requests.get(pipelines_url, gl.data).json()
    if not isinstance(pipelines, list):
        return MRPipelineLookup(status="excluded", reason="unable to list MR pipelines")

    finished_statuses = {"success", "failed", "canceled"}
    for pipeline in pipelines:
        if pipeline.get("status") in finished_statuses:
            return MRPipelineLookup(status="pipeline", pipeline_id=str(pipeline["id"]))

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
    url = gl.base_url + f"/projects/{project_id}/pipelines/{pipeline_id}/jobs"
    jobs = requests.get(url, gl.data).json()
    for job in jobs:
        if job.get("name") == job_name:
            return job["id"]
    return None


def download_job_artifact(gl, project_id, job_id, artifact_path):
    """Download artifact_path from a job and return the path to a temp file."""
    url = (
        gl.base_url + f"/projects/{project_id}/jobs/{job_id}/artifacts/{artifact_path}"
    )
    response = requests.get(url, gl.data, stream=True)
    response.raise_for_status()
    suffix = os.path.splitext(artifact_path)[1]
    with tempfile.NamedTemporaryFile("wb", suffix=suffix, delete=False) as f:
        for chunk in response.iter_content(chunk_size=8192):
            f.write(chunk)
        return f.name


def trigger_pipeline(gl, project_id, ref, variables=None):
    """Trigger a pipeline on ref and return (pipeline_id, web_url).

    variables, if provided, is a dict of variable names to string values.
    """
    url = gl.base_url + f"/projects/{project_id}/pipeline"
    payload = {"ref": ref}
    if variables:
        payload["variables"] = [{"key": k, "value": v} for k, v in variables.items()]
    response = requests.post(url, params=gl.data, json=payload)
    response.raise_for_status()
    data = response.json()
    return data["id"], data.get("web_url", "")


_TERMINAL_STATUSES = {"success", "failed", "canceled", "skipped"}


def wait_for_pipeline(gl, project_id, pipeline_id, poll_interval=30):
    """Poll pipeline until it reaches a terminal status.

    Prints a status line each poll cycle and returns the final status string.
    """
    url = gl.base_url + f"/projects/{project_id}/pipelines/{pipeline_id}"
    while True:
        response = requests.get(url, gl.data)
        response.raise_for_status()
        status = response.json().get("status", "unknown")
        print(f"  pipeline {pipeline_id}: {status}")
        if status in _TERMINAL_STATUSES:
            return status
        time.sleep(poll_interval)
