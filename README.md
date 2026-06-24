# LeanDatabase

LeanDatabase provides a small HTTP server for checking equivalence of SQL-like
queries using Lean. The Python entry point is `sql_server.py`; it starts the Lean
executable `sql_process` through Lake and exposes an HTTP endpoint.

## Run With Docker

Build the image from the repository root:

```sh
docker build -t lean-database-sql .
```

Run the server on port `6767`:

```sh
docker run --rm -p 6767:6767 lean-database-sql
```

Open the demo page:

```sh
open http://127.0.0.1:6767/
```

Or test the JSON endpoint:

```sh
curl -sS \
  -H 'Content-Type: application/json' \
  --data '{"schema":[{"name":"age","type":"Int"},{"name":"isActive","type":"Bool"}],"first":"SELECT * FROM table WHERE age > 30 && isActive","second":"SELECT * FROM table WHERE age > 30 && isActive"}' \
  http://127.0.0.1:6767/
```

If Docker Desktop installed the CLI but `docker` is not on your `PATH`, use:

```sh
/Applications/Docker.app/Contents/Resources/bin/docker build -t lean-database-sql .
/Applications/Docker.app/Contents/Resources/bin/docker run --rm -p 6767:6767 lean-database-sql
```

## Run Locally

Install elan, which installs and manages the Lean toolchain:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Restart the shell or load elan into the current shell:

```sh
source "$HOME/.elan/env"
```

Fetch dependencies and pull the Mathlib cache:

```sh
lake exe cache get
```

Build the Lean library and server process:

```sh
lake build LeanDatabase sql_process
```

Start the Python HTTP server:

```sh
python3 sql_server.py --host 127.0.0.1 --port 6767
```

Then open:

```sh
open http://127.0.0.1:6767/
```

The server prints `sql_process is ready` when the Lean subprocess has finished
initializing and requests can be processed.
