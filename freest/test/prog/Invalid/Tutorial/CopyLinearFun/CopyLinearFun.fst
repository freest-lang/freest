module CopyLinearFun where

double : Int -1-> Int
double x = x + x

copy : ()
copy = 
    print (double 5 + double 5)