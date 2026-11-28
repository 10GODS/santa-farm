$ErrorActionPreference = "Stop"
$tok = (Get-Content "$env:USERPROFILE\.github_token" -Raw).Trim()
$headers = @{ Authorization = "Bearer $tok"; "User-Agent" = "santa-farm"; Accept = "application/vnd.github+json" }
$me = Invoke-RestMethod -Uri "https://api.github.com/user" -Headers $headers
Write-Host "login: $($me.login)"
try {
  Invoke-RestMethod -Method Post -Uri "https://api.github.com/user/repos" -Headers $headers -Body (@{ name = "santa-farm"; public = $true; description = "Distributed value-set annealing (setwalk) on GitHub Actions - Santa 2026. Engines credited: Ross Wade (CC0), goodpjw2008, Atakan Aldemir." } | ConvertTo-Json) | Out-Null
  Write-Host "repo created"
} catch { Write-Host "repo create skipped/exists: $($_.Exception.Response.StatusCode)" }
$env:GIT_TERMINAL_PROMPT = "0"
Set-Location "$env:USERPROFILE\santa-farm"
git init -q 2>$null
git add -A
git -c user.name="saurabhkumar234" -c user.email="saurabhkumar234@users.noreply.github.com" commit -qm "santa-farm: setwalk 20-shard referee-gated worker"
git remote remove origin 2>$null
git remote add origin "https://x-access-token:${tok}@github.com/$($me.login)/santa-farm.git"
git push -uf origin HEAD:master
Write-Host "pushed. triggering dispatch..."
Invoke-RestMethod -Method Post -Uri "https://api.github.com/repos/$($me.login)/santa-farm/actions/workflows/farm.yml/dispatches" -Headers $headers -Body (@{ ref = "master"; inputs = @{ nshard = "20"; secs = "45"; seed = "777000" } } | ConvertTo-Json)
Write-Host "DONE - farm running on 20 ubuntu runners"
