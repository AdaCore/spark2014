package body Multiset with SPARK_MOde => On is
   use Maps;

function Cardinality (Container : Multiset) return Big_Natural is
   (Container.Card);

   ---------------------
   -- Cardinality_Rec --
   ---------------------

   function Cardinality_Rec (Container : Maps.Map) return Big_Natural is
    (if Length (Container) = 0 then 0
     else Get (Container, Choose (Container))
            + Cardinality_Rec (Remove (Container, Choose (Container))));

   --------------
   -- Contains --
   --------------

   function Contains
     (Container : Multiset;
      Element   : Element_Type) return Boolean is
   begin
      return Has_Key (Container.Map, Element);
   end Contains;

   ------------
   -- Choose --
   ------------

   function Choose (Container : Multiset) return Element_Type is
      (Choose (Container.Map));

   function Empty_Multiset return Multiset is
   begin
      return (others => <>);
   end Empty_Multiset;

   function Invariant (Container : Multiset) return Boolean is
      (Container.Card = Cardinality_Rec (Container.Map));

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Multiset) return Boolean is
      Is_Empty_Result : constant Boolean := Is_Empty (Container.Map);
   begin
      return Is_Empty_Result;
   end Is_Empty;

   ------------------
   -- Nb_Occurence --
   ------------------

   function Nb_Occurence
     (Container : Multiset;
      Element   : Element_Type) return Big_Natural
   is (if Has_Key (Container.Map, Element)
       then  Get (Container.Map, Element)
       else 0);

end Multiset;
