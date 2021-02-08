procedure Null_Exclusion_Borrow with SPARK_Mode is
   type List_Cell;
   type List is access List_Cell;
   type List_Cell is record
      K : Integer;
      E : Integer;
      N : List;
   end record;

   procedure Bad_Update (X : List; K, E : Integer) is
      B : not null access List_Cell := X; --@NULL_EXCLUSION:FAIL
   begin
      loop
         if B.K = K then
            exit;
         end if;
         B := B.N; --@NULL_EXCLUSION:FAIL
      end loop;
      B.E := E;
   end Bad_Update;

   procedure Ok_Update (X : in out List; K, E : Integer) is
   begin
      if X = null then
         X := new List_Cell'(K => K,
                             E => E,
                             N => null);
         return;
      end if;

      declare
         B : not null access List_Cell := X; --@NULL_EXCLUSION:PASS
      begin
         loop
            if B.K = K then
               B.E := E;
               exit;
            elsif B.N = null then
               B.N := new List_Cell'(K => K,
                                     E => E,
                                     N => null);
               B := B.N;
               exit;
            end if;
            B := B.N; --@NULL_EXCLUSION:PASS
         end loop;
      end;
   end Ok_Update;

begin
   null;
end Null_Exclusion_Borrow;
