package Flow is

   type Infos is array (Boolean) of Boolean;

   type Flow_Analysis_Graphs_Root
   is record
      Tasking : Infos;
   end record;

   function Is_Valid (X : Flow_Analysis_Graphs_Root) return Boolean;

end Flow;
