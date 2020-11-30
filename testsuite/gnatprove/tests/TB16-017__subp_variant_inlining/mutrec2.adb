with Text_IO;
procedure MutRec2 with SPARK_Mode Is
   pragma Assertion_Policy (Check);

   function Inc (X : Integer) return Long_Integer;
   function Dec (X : Integer) return Long_Integer;

   procedure Proc1 (M, N : in out Integer)
     with Subprogram_Variant => (Decreases => Inc (N))
   ;
   procedure Proc2 (N, M : in out Integer)
     with Subprogram_Variant => (Decreases => Dec (N))
   ;
   procedure Proc1 (M, N : in out Integer) is
      Flag : constant Boolean := M <= N;
   begin
      Text_IO.Put_Line ("Proc1, M =" & M'Image & ", N =" & N'Image);
      if N = Integer'First or M = Integer'Last then
         return;
      end if;
      N := N - 1;
      M := M + 1;
      if Flag then
         Proc2 (M, N);
      end if;
   end Proc1;
   procedure Proc2 (N, M : in out Integer) is
      Flag : constant Boolean := M <= N;
   begin
      Text_IO.Put_Line ("Proc2, M =" & M'Image & ", N =" & N'Image);
      if N = Integer'First or M = Integer'Last then
         return;
      end if;
      N := N - 1;
      M := M + 1;
      if Flag then
         Proc1 (M, N);
      end if;
   end Proc2;

   function Inc (X : Integer) return Long_Integer is
   begin
      return Long_Integer (X) + 123;
   end Inc;

   function Dec (X : Integer) return Long_Integer is
   begin
      return Long_Integer (X) - 456;
   end Dec;

   X, Y : Integer := 0;
begin
   Proc1 (X, Y);
   Text_IO.Put_Line ("Mutrec, X =" & X'Image & ", Y =" & Y'Image);
end MutRec2;
