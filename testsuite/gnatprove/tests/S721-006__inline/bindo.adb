package body Bindo is

   ----------
   -- Kind --
   ----------

   function Kind
     (G    : Library_Graph;
      Edge : Library_Graph_Edge_Id) return Library_Graph_Edge_Kind
   is
      pragma Unreferenced (G, Edge);
   begin
      return No_Edge;
   end Kind;

   ----------------------------------------
   -- Decrement_Library_Graph_Edge_Count --
   ----------------------------------------

   procedure Decrement_Library_Graph_Edge_Count
     (G    : Library_Graph;
      Kind : Library_Graph_Edge_Kind)
   is
      Count : Natural renames G.Counts (Kind);

   begin
      Count := Count - 1;
   end Decrement_Library_Graph_Edge_Count;

   -----------------
   -- Delete_Edge --
   -----------------

   procedure Delete_Edge
     (G    : Library_Graph;
      Edge : Library_Graph_Edge_Id)
   is
   begin
      Decrement_Library_Graph_Edge_Count (G, Kind (G, Edge));
   end Delete_Edge;

end Bindo;
