import os
from pathlib import Path
import http.server
import socketserver

from invoke import run, task

BP_DIR = Path(__file__).parent

@task
def authors(ctx):
    cwd = os.getcwd()
    with open('./authors') as f:
        authors = ', '.join(f.read().splitlines())
    run(f"sed 's/<<authors>>/{authors}/g' ./docs_src/template_src.html > ./docs_src/template.html")
    run(f"sed 's/<<authors>>/{authors}/g' ./blueprint/src/print_src.tex > ./blueprint/src/print.tex")
    run(f"sed 's/<<authors>>/{authors}/g' ./blueprint/src/web_src.tex > ./blueprint/src/web.tex")

@task(authors)
def print(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
    os.chdir(cwd)

@task(authors)
def bp(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
    run('cd src && xelatex -output-directory=../print print.tex')
    os.chdir(cwd)


@task(authors)
def web(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR/'src')
    run('plastex -c plastex.cfg web.tex')
    os.chdir(cwd)

@task
def serve(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR/'web')
    Handler = http.server.SimpleHTTPRequestHandler
    httpd = socketserver.TCPServer(("", 8000), Handler)
    httpd.serve_forever()
    os.chdir(cwd)
