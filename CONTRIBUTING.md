# Contributing

Contributions are welcome as small, reviewable changes. Each one has to pass `go test ./...`, which includes the conformance corpus and the second verifier in `tools/verify-py`.

The repository contains no emoji and no decorative pictographs, in code, comments, documentation, commit messages or headings. This is enforced mechanically. `go test ./tools/noemoji` fails on any line that contains one, and the same tool removes them:

    go run ./tools/noemoji          # list offending lines, exit 1 if any
    go run ./tools/noemoji -fix     # remove them in place

The reason is the same one that governs the language itself. A symbol in this project is conventional and not pictorial: an atom is an opaque name, the reducer never looks inside it, and whatever meaning it has comes from the rules and permissions that act on it. A letter works this way, since nothing in its shape says what it refers to. An emoji does not. It resembles its referent, and the resemblance has to be drawn by someone, so it carries choices of skin, style, gesture and typical example that the project has not made, and it is drawn differently on each platform, so the author cannot know what a reader will see. A name given to a character in a novel places that character in an age and a region before anything else is said, and a pictograph does the same at scale. Plain text is a neutral medium in which any sound, motion, word or structure can be represented without importing those choices.

File names use only letters, digits, dot, underscore and hyphen, since other characters behave differently across shells, URLs and operating systems.

Prose is written in plain sentences and avoids dashes used as punctuation. Claims about the project use the vocabulary of `notes/claim-status.md`: a result is proved, computationally tested, established by implementation design, or open, and a change that adds a claim says which of these it is and what bounds apply. Words such as independent, verified or complete are used only when the evidence in that document supports them.
