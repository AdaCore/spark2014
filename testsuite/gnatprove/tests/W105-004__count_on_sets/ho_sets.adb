package body HO_Sets with SPARK_Mode is

   function Count
     (Container : Set;
      Test      : not null access function (Item : Integer) return Boolean)
      return Big_Integer
   is
     (if Is_Empty (Container) then Big_Integer'(0)
      else (if Test (Choose (Container)) then Big_Integer'(1) else Big_Integer'(0))
      + Count (Remove (Container, Choose (Container)), Test));

   procedure Lemma_Count_Eq
     (Left, Right : Set;
      Test        : not null access function (Item : Integer) return Boolean)
   is
   begin
      if Length (Left) /= 0 then
         declare
            E : constant Integer := Choose (Right);
         begin
            Lemma_Count_Remove (Left, E, Test);
            Lemma_Count_Eq (Remove (Left, E), Remove (Right, E), Test);
         end;
      end if;
   end Lemma_Count_Eq;

   procedure Lemma_Count_Remove
     (Container : Set;
      Item      : Integer;
      Test      : not null access function (Item : Integer) return Boolean)
   is
      L : constant Integer := Choose (Container);
   begin
      if Item /= L then
         Lemma_Count_Remove (Remove (Container, L), Item, Test);
         Lemma_Count_Eq (Remove (Remove (Container, L), Item), Remove (Remove (Container, Item), L), Test);
         Lemma_Count_Remove (Remove (Container, Item), L, Test);
      end if;
   end Lemma_Count_Remove;

end HO_Sets;
