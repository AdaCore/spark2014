package body Graphs
  with SPARK_Mode => On
is

   -----------------
   -- Empty_Graph --
   -----------------

   function Empty_Graph (Size : Vertex_Count) return Graph is
     (Size => Size,
      Adj  => [for I in 1 .. Size => [for J in 1 .. Size => No_Edge]]);

   --------------
   -- Symmetry --
   --------------

   procedure Symmetry (G : Graph; U, V : Vertex) is null;

   function Restrict (G : Graph; Threshold : Weight_Threshold) return Graph is
     (Size => G.Size,
      Adj  =>
        [for I in 1 .. G.Size =>
           [for J in 1 .. G.Size =>
              (if G.Adj (I, J).Present and then G.Adj (I, J).Length <= Threshold
               then G.Adj (I, J) else No_Edge)]]);

   procedure No_Self_Loop (G : Graph; V : Vertex) is null;
   --  Has_Edge (G, V, V) = G.Adj (V, V).Present, false by the Loop_Free predicate.
   --  Nothing to prove at run time; the postcondition follows because
   --  Has_Edge / Edge_Length read the canonical cell (Lo, Hi), and Lo and Hi
   --  are symmetric in U and V.

   --------------
   -- Add_Edge --
   --------------

   procedure Add_Edge (G : in out Graph; U, V : Vertex; Length : Weight) is
   begin
      --  U /= V (precondition) means Lo (U, V) < Hi (U, V): the write lands
      --  off the diagonal, so the Loop_Free predicate is preserved.
      G.Adj (Lo (U, V), Hi (U, V)) := (Present => True, Length => Length);
   end Add_Edge;

   -----------------
   -- Remove_Edge --
   -----------------

   procedure Remove_Edge (G : in out Graph; U, V : Vertex) is
   begin
      --  Writing No_Edge (an absent edge) preserves Loop_Free even on the
      --  diagonal, so no precondition on the relative order of U, V is needed.
      G.Adj (Lo (U, V), Hi (U, V)) := No_Edge;
   end Remove_Edge;

   ------------
   -- Degree --
   ------------

   function Degree (G : Graph; Source : Vertex) return Degree_Count is
      Count : Degree_Count := 0;
   begin
      for V in Vertex range 1 .. G.Size loop
         if Has_Edge (G, Source, V) then
            Count := Count + 1;
         end if;
         pragma Loop_Invariant (Count <= V);
         pragma Loop_Invariant
           ((Count = 0) =
              (for all W in Vertex range 1 .. V => not Has_Edge (G, Source, W)));
      end loop;
      return Count;
   end Degree;

end Graphs;
