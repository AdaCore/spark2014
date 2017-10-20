package body Flow is

   function Is_Valid (X : Flow_Analysis_Graphs_Root)
                      return Boolean
   is (for all Info of X.Tasking => Info);

end Flow;
