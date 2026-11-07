package supervised

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"strconv"

	"github.com/standardgalactic/spherepop-kernel/reduce"
)

// AuditFormat identifies the layout of an audit log.
const AuditFormat = "supervised-audit/1"

// Entry is one decision. A refusal leaves the term unchanged, so its After is
// the digest of the term the proposal was made against.
type Entry struct {
	Seq      int    `json:"seq"`
	Rule     string `json:"rule"`
	Path     string `json:"path"`
	Decision string `json:"decision"`
	Mask     string `json:"mask"`
	After    string `json:"after"`
	Link     string `json:"link"`
}

// Audit is the whole record of a supervised run.
type Audit struct {
	Format      string            `json:"format"`
	Config      reduce.ConfigSpec `json:"config"`
	Start       string            `json:"start"`
	StartDigest string            `json:"start_digest"`
	Strategy    string            `json:"strategy"`
	Fuel        uint64            `json:"fuel"`
	Entries     []Entry           `json:"entries"`
	Final       string            `json:"final"`
	FinalDigest string            `json:"final_digest"`
	Exhausted   bool              `json:"exhausted"`
	Head        string            `json:"head"`
}

func sum(parts ...[]byte) string {
	h := sha256.New()
	for _, p := range parts {
		h.Write(p)
		h.Write([]byte{0})
	}
	return hex.EncodeToString(h.Sum(nil))
}

func configDigest(s reduce.ConfigSpec) (string, error) {
	b, err := json.Marshal(s)
	if err != nil {
		return "", err
	}
	return sum([]byte("supervised-config/1"), b), nil
}

func genesis(startDigest, cfgDigest string) string {
	return sum([]byte(AuditFormat), []byte(startDigest), []byte(cfgDigest))
}

func link(prev string, e Entry) string {
	return sum([]byte(prev), []byte(strconv.Itoa(e.Seq)), []byte(e.Rule), []byte(e.Path),
		[]byte(e.Decision), []byte(e.Mask), []byte(e.After))
}

// Seal recomputes every link and the head from the entries as they stand.
func Seal(a *Audit) error {
	cd, err := configDigest(a.Config)
	if err != nil {
		return err
	}
	prev := genesis(a.StartDigest, cd)
	for i := range a.Entries {
		a.Entries[i].Link = link(prev, a.Entries[i])
		prev = a.Entries[i].Link
	}
	a.Head = prev
	return nil
}

// Marshal encodes a as indented JSON with a trailing newline.
func Marshal(a Audit) ([]byte, error) {
	b, err := json.MarshalIndent(a, "", "  ")
	if err != nil {
		return nil, err
	}
	return append(b, '\n'), nil
}

// Unmarshal decodes a log and rejects unknown fields.
func Unmarshal(b []byte) (Audit, error) {
	var a Audit
	dec := json.NewDecoder(bytes.NewReader(b))
	dec.DisallowUnknownFields()
	err := dec.Decode(&a)
	return a, err
}
