# Put the research on GitHub

You can do this in your browser; no Lean installation is needed.

1. Extract **xi-family-github.zip**, then open the **xi-family-github** folder inside it.
2. Go to [New repository](https://github.com/new). Name it **xi-family**, choose **Public**, leave the extra initialization options off, and click **Create repository**.
3. Click **uploading an existing file** (or **Add file → Upload files**). Drag **everything inside the extracted folder** into the upload area, including **.github**. Upload the contents, not the ZIP or the enclosing folder.
4. Commit the files directly to **main**, with a message such as **Paper and complete Lean proof**. The bundle contains 100 files, within [GitHub's browser upload limit](https://docs.github.com/en/repositories/working-with-files/managing-files/adding-a-file-to-a-repository).
5. Open **Actions → Verify Lean** and open the latest run. Wait for its green check. If needed, click **Run workflow → Run workflow**. See [GitHub's manual-run instructions](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/manually-run-a-workflow).
6. Share the repository link and the successful Actions-run link. Readers can open the paper, browse the proof, and reproduce the checks.

**If “Verify Lean” is missing:** on the Code page, check that **.github/workflows/verify.yml** exists at the repository root. If it was skipped, use **Add file → Create new file**, enter that exact path, paste the supplied workflow's contents, and commit it. Do not place it inside an extra enclosing folder.

The green check confirms that the formal proof build and axiom checks passed for that commit. [REVIEWER-GUIDE.md](REVIEWER-GUIDE.md) helps a mathematician independently check that the statements match the paper.
