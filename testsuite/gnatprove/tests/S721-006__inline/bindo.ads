package Bindo is

   ------------------------
   -- Library graph edge --
   ------------------------

   --  The following type denotes a library graph edge handle

   type Library_Graph_Edge_Id is new Natural;

   --  The following type represents the various kinds of library edges

   type Library_Graph_Edge_Kind is
     (No_Edge);

   ----------------
   -- Statistics --
   ----------------

   type Library_Graph_Edge_Counts is
     array (Library_Graph_Edge_Kind) of Natural;

   --  The following type represents the attributes of a library graph

   type Library_Graph_Attributes is record
      Counts : Library_Graph_Edge_Counts := (others => 0);
      --  Edge statistics
   end record;

   -----------
   -- Graph --
   -----------

   --  The following type denotes a library graph handle. Each instance must
   --  be created using routine Create.

   type Library_Graph is access Library_Graph_Attributes;

   -----------------
   -- Delete_Edge --
   -----------------

   procedure Delete_Edge
     (G    : Library_Graph;
      Edge : Library_Graph_Edge_Id);

end Bindo;
