start=0$1
(for i in `seq $start 100`; do echo $i; sleep 1; echo --------; sleep 1; env R=$i python3 bin/mychains.py subjects/urlparser_hard.py; done ) 2>&1 | tee urlparser.log
