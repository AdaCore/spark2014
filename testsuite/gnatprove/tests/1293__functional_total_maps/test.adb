with Ada.Text_IO;
with Inst;
use Inst.Int_Total_Maps;

procedure Test with SPARK_Mode is

   procedure Assert (B : Boolean; S : String)
   with Pre => B;
   procedure Assert (B : Boolean; S : String) is
   begin
      if not B then
         Ada.Text_IO.Put_Line (S);
      end if;
   end Assert;

   procedure Test_Default_Map is
      X : Map := Default_Map;
   begin
      Assert
        (Get (X, 0) = 0, "Default_Map: Get returns Default_Element for 0");
      Assert
        (Get (X, 5) = 0, "Default_Map: Get returns Default_Element for 5");
      Assert
        (Get (X, 42) = 0, "Default_Map: Get returns Default_Element for 42");
   end Test_Default_Map;

   procedure Test_Default_Init is
      X : Map;
   begin
      Assert
        (Get (X, 0) = 0, "Default_Init: Get returns Default_Element for 0");
      Assert
        (Get (X, 5) = 0, "Default_Init: Get returns Default_Element for 5");
      Assert
        (Get (X, 42) = 0, "Default_Init: Get returns Default_Element for 42");
      Assert (X = Default_Map, "Default_Init: equals Default_Map");
   end Test_Default_Init;

   procedure Test_Get is
      X : Map;
   begin
      X := Set (X, 5, 42);
      Assert (Get (X, 5) = 42, "Get: returns set value");
      Assert (Get (X, 105) = 42, "Get: returns same value for equivalent key");
      Assert (Get (X, 6) = 0, "Get: returns Default_Element for unset key");
      Assert
        (Get (X, 106) = 0,
         "Get: returns Default_Element for unset equivalent key");
   end Test_Get;

   procedure Test_Eq is
      X, Y : Map;
   begin
      Assert (X = Y, """="" on default-initialized maps");
      X := Set (X, 5, 42);
      Assert (X /= Y, """="" on maps with different values");
      Y := Set (Y, 5, 42);
      Assert (X = Y, """="" on maps with same explicit entry");
      --  Setting a key to Default_Element is the same as the default map
      X := Set (Default_Map, 5, 0);
      Assert
        (X = Default_Map, """="" explicit Default_Element equals Default_Map");
      --  Equality uses equivalence on keys
      X := Set (Default_Map, 5, 42);
      Y := Set (Default_Map, 105, 42);
      Assert (X = Y, """="" uses equivalence on keys");
      --  Equality uses user-defined equality on elements
      X := Set (Default_Map, 5, 42);
      Y := Set (Default_Map, 5, 1042);
      Assert (X = Y, """="" uses user-defined equality on elements");
      --  Different values yield unequal maps
      X := Set (Default_Map, 5, 42);
      Y := Set (Default_Map, 5, 43);
      Assert (X /= Y, """="" detects different elements");
      --  Maps differing on unset keys: one set to non-default, other not
      X := Set (Default_Map, 5, 42);
      Y := Default_Map;
      Assert (X /= Y, """="" detects value set only in one map");
   end Test_Eq;

   procedure Test_Equivalent_Maps is
      X, Y : Map;
   begin
      Assert (Equivalent_Maps (X, Y), "Equivalent_Maps on default maps");
      X := Set (Default_Map, 5, 42);
      Assert
        (not Equivalent_Maps (X, Y),
         "Equivalent_Maps on maps with different values");
      --  Uses equivalence on both keys and elements: 42 equiv 142, 5 equiv 105
      Y := Set (Default_Map, 105, 142);
      Assert
        (Equivalent_Maps (X, Y),
         "Equivalent_Maps uses key and element equivalence");
      Y := Set (Default_Map, 5, 43);
      Assert
        (not Equivalent_Maps (X, Y),
         "Equivalent_Maps detects non-equivalent elements");
   end Test_Equivalent_Maps;

   procedure Test_Set is
      X : Map;
   begin
      X := Set (X, 5, 42);
      Assert (Get (X, 5) = 42, "Set: value is stored");
      Assert (Get (X, 7) = 0, "Set: unrelated key is unchanged");
      --  Overwrite an existing entry
      X := Set (X, 5, 99);
      Assert (Get (X, 5) = 99, "Set: overwrite updates value");
      Assert (Get (X, 7) = 0, "Set: overwrite leaves unrelated key unchanged");
      --  Setting via an equivalent key
      X := Set (Default_Map, 105, 77);
      Assert (Get (X, 5) = 77, "Set: via equivalent key affects whole class");
      Assert (Get (X, 205) = 77, "Set: get via another equivalent key works");
      --  Multiple distinct keys
      X := Set (Default_Map, 3, 10);
      X := Set (X, 7, 20);
      Assert (Get (X, 3) = 10, "Set: first entry preserved after second Set");
      Assert (Get (X, 7) = 20, "Set: second entry accessible");
      Assert (Get (X, 1) = 0, "Set: unset key still returns Default_Element");
   end Test_Set;

   procedure Test_Aggregate is
      X : Map := [5 => 42, 7 => 99];
   begin
      Assert (Get (X, 5) = 42, "Aggregate: first entry");
      Assert (Get (X, 7) = 99, "Aggregate: second entry");
      Assert (Get (X, 105) = 42, "Aggregate: equivalent key of first entry");
      Assert (Get (X, 107) = 99, "Aggregate: equivalent key of second entry");
      Assert (Get (X, 1) = 0, "Aggregate: unset key returns Default_Element");
   end Test_Aggregate;

begin
   Test_Default_Map;
   Test_Default_Init;
   Test_Get;
   Test_Eq;
   Test_Equivalent_Maps;
   Test_Set;
   Test_Aggregate;
end Test;
