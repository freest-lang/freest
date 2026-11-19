basic : String
basic =
  """
  Line 1
  Line 2
  """

nested : String
nested =
  """
    <div>
      <p>ABC</p>

    </div>
  """

firstLine : String
firstLine = """Test
  Line 1
  """

keepIndent : String
keepIndent =
  """
  \&  Line 1
  \&  Line 2
  """

gapEnd : String
gapEnd =
  """
  Line 1
  Line 2\
  \"""

quotes : String
quotes = """say "hi", "" and \""" here"""

escapes : String
escapes =
  """
  a\nb\t\65
  """

tabbed : String
tabbed =
  """
	Line 1
	  Line 2
	"""

empty : String
empty = """"""

main : ()
main =
  print basic; print nested; print firstLine; print keepIndent;
  print gapEnd; print quotes; print escapes; print tabbed; print empty
