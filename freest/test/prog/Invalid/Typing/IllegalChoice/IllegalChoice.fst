module IllegalChoice where

foo : +{A: Skip} -> Skip
foo c = select B c
