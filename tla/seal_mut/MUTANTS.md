# CalmSeal — ένα mutant ανά invariant (17/10/2026)

`CalmSealMut.tla` = `../CalmSeal.tla` + σταθερά `Mut`. Μικρό μοντέλο (`MC_CalmSealMut.tla`): 3 κόμβοι, **2** γεγονότα, πλειοψηφίες, MaxSilent=1
(το πλήρες `../MC_CalmSeal.cfg` με 3 γεγονότα θέλει 1 h· εκεί το κανονικό μοντέλο: No error, 303.544.256 καταστάσεις).

| invariant | mutant | αποτέλεσμα |
|---|---|---|
| TypeOK | `BadVote`: ψήφος «maybe» | violated |
| Agreement | `WeakQuorum`: ένας ψήφος «absent» αρκεί | violated |
| UniqueChoice | `WeakQuorum` | violated |
| NotBoth | `WeakQuorum` | violated |
| Validity | `Invent`: ο αργός δρόμος γράφει Ev αντί για ό,τι στάλθηκε | violated |
| FastExcludesAbsent | `FastEarly`: γρήγορο τέλος με το δικό του HaveAll, χωρίς των άλλων | violated |
| Inv | `WeakQuorum` | violated |

⚠️ Πρώτη απόπειρα για το FastExcludesAbsent (`FastIgnoresVotes`: χωρίς τους ελέγχους «όχι absent» στο HaveAll/VoteAbsent) **δεν** έσπασε
σε 100 εκ. καταστάσεις — οι έλεγχοι ήταν περιττοί (HaveAll ⇒ heard = Node ⇒ κανένα absent). Λάθος του mutant, όχι κενό του κανόνα.
