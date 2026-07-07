linDouble : Int -1-> Int
linDouble x = x + x

copy : ()
copy = 
    print (linDouble 5 + linDouble 5)
