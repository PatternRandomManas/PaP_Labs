/-!
# Registration

* fill in your name, github username, zulip handle, and url for your lab repo.
* check details with `#eval details?`
* the command `lake exe lab1` should now work and give details about your registration.
* commit and push your changes to your repo.
-/
def name?: Option String := "Manas Kaushik Das"
def github?: Option String := "PatternRandomManas"
def zulip?: Option String := "Manas Kaushik Das"
def lab_repo?: Option String := "https://github.com/PatternRandomManas/PaP_Labs.git"

def details? : Option String := do
  let name ← name?
  let github ← github?
  let zulip ← zulip?
  let lab_repo ← lab_repo?
  pure $ s!"Name: {name}; Gihub username:{github}; Zulip handle: {zulip}; Lab repo url: {lab_repo})"

#eval details?

