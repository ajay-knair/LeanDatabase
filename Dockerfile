FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive
ENV ELAN_HOME=/root/.elan
ENV PATH=/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

WORKDIR /app

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        git \
        python3 \
        build-essential \
        zstd \
    && rm -rf /var/lib/apt/lists/*

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none

COPY lean-toolchain lakefile.toml lake-manifest.json ./

RUN lean --version \
    && lake --version \
    && lake exe cache get

COPY LeanDatabase ./LeanDatabase
COPY Examples ./Examples
COPY LeanDatabase.lean sql_process.lean sql_server.py ./

RUN lake build LeanDatabase sql_process

EXPOSE 6767

CMD ["python3", "sql_server.py", "--host", "0.0.0.0", "--port", "6767"]
