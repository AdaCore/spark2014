package My_Container_Model with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);
   Max : constant := 100;

   type Container is private with
     Iterable => (First       => First,
                  Has_Element => Has_Element,
                  Next        => Next,
                  Element     => Element);

   type Model is private with
     Iterable => (First       => M_First,
                  Has_Element => M_Has_Element,
                  Next        => M_Next,
                  Element     => M_Element);

   type Cursor is private;

   function Get_Model (C : Container) return Model;

   function Valid (E : Natural) return Boolean;

   procedure Modify (C : in out Container) with
     Post => (for all E of C => Valid (E));

   function First (C : Container) return  Cursor;
   function Next (C : Container; P : Cursor) return Cursor with
     Pre => Has_Element (C, P);
   function Has_Element (C : Container; P : Cursor) return Boolean;
   function Element (C : Container; P : Cursor) return Natural with
     Pre => Has_Element (C, P);
   pragma Annotate
     (GNATprove, Iterable_For_Proof, "Model", Entity => Get_Model);

   function M_First (C : Model) return Natural;
   function M_Next (C : Model; P : Natural) return Natural with
     Pre => M_Has_Element (C, P);
   function M_Has_Element (C : Model; P : Natural) return Boolean;
   function M_Element (C : Model; P : Natural) return Natural with
     Pre => M_Has_Element (C, P);
private
   subtype My_Index is Natural range 1 .. Max;
   type Container is array (My_Index) of Natural;
   type Model is array (My_Index) of Natural;

   type Cursor is record
      Index : Natural;
   end record;
end My_Container_Model;
