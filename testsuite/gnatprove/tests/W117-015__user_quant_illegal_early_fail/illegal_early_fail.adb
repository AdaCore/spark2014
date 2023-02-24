procedure Illegal_Errors with SPARK_Mode is


   type Boolean_Cursor is new Integer range 0 .. 2;

   generic
   package Make_Boolean_Container is

      --  Variants of this package are inserted anywhere.
      --  However, cannot always use the generic directly
      --  since Model/Contains need to be declared
      --  in same list as container type.

      type Boolean_Container is (Booleans)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (X : Boolean_Container) return Boolean_Cursor is (0);
      function Next (X : Boolean_Container; C : Boolean_Cursor)
                     return Boolean_Cursor
      is (if C /= 2 then C + 1 else C);
      function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                            return Boolean
      is (C /= 2);
      function Element (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean
      is (C /= 0);
   end Make_Boolean_Container;

   package Ill_Placed_Annotation is

      --  Annotation must immediately follow 'Element' declaration.

      type Boolean_Container is (Booleans)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (X : Boolean_Container) return Boolean_Cursor is (0);
      function Next (X : Boolean_Container; C : Boolean_Cursor)
                     return Boolean_Cursor
      is (if C /= 2 then C + 1 else C);
      function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                            return Boolean
      is (C /= 2);
      function Element (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean
      is (C /= 0);
      function Contains (X : Boolean_Container; B : Boolean) return Boolean
      is (True);
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
      --  FAILS (too late).

   end Ill_Placed_Annotation;

   package Model_Cycles is

      --  Cycle of model functions forbidden in SPARK.

      package Looping is

         --  Loop over itself.

         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Boolean_Container) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                               return Boolean
         is (C /= 2);
         function Model (X : Boolean_Container) return Boolean_Container
         is (X);
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                           return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "model", Model);
         --  FAILS.
      end Looping;

      package Model_Loop is
         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         type Boolean_Container2 is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         type Boolean_Container3 is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Boolean_Container) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                               return Boolean
         is (C /= 2);
         function First (X : Boolean_Container2) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container2; C : Boolean_Cursor)
                        return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container2; C : Boolean_Cursor)
                               return Boolean
         is (C /= 2);
         function First (X : Boolean_Container3) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container3; C : Boolean_Cursor)
                        return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container3; C : Boolean_Cursor)
                               return Boolean
         is (C /= 2);

         function C12 (X : Boolean_Container) return Boolean_Container2
           with Import, Global => null, Annotate => (GNATprove, Always_Return);
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                           return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "model", C12);
         function C23 (X : Boolean_Container2) return Boolean_Container3
           with Import, Global => null, Annotate => (GNATprove, Always_Return);
         function Element (X : Boolean_Container2; C : Boolean_Cursor)
                           return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "model", C23);
         function C31 (X : Boolean_Container3) return Boolean_Container
           with Import, Global => null, Annotate => (GNATprove, Always_Return);
         function Element (X : Boolean_Container3; C : Boolean_Cursor)
                           return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "model", C31);
         --  This one fails, cycle 1 --C12-> 2 --C23-> 3 --C31->  1.
      end Model_Loop;

   end Model_Cycles;

   package Not_Same_Elements is

      --  Model function between containers with different types for
      --  element is not allowed in SPARK.

      package B0 is new Make_Boolean_Container;
      use B0;

      type Other_Boolean is (Fake_False, Fake_True);
      function Cast (B : Boolean) return Other_Boolean is
        (if B then Fake_True else Fake_False);
      type Other_Boolean_Container is (Other_Booleans)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (X : Other_Boolean_Container) return Boolean_Cursor
      is (0);
      function Next (X : Other_Boolean_Container; C : Boolean_Cursor)
                     return Boolean_Cursor
      is (if C /= 2 then C + 1 else C);
      function Has_Element (X : Other_Boolean_Container; C : Boolean_Cursor)
                            return Boolean
      is (C /= 2);
      function Model (X : Other_Boolean_Container) return Boolean_Container
      is (Booleans);
      function Element (X : Other_Boolean_Container; C : Boolean_Cursor)
                        return Other_Boolean
      is (Cast (C /= 0));
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Model);
      --  FAILS.

   end Not_Same_Elements;

   package No_Globals_In_Model is

      --  Model function not allowed to access global data.

      package B0 is new Make_Boolean_Container;
      type Boolean_Container is (Booleans)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (X : Boolean_Container) return Boolean_Cursor is (0);
      function Next (X : Boolean_Container; C : Boolean_Cursor)
                     return Boolean_Cursor
      is (if C /= 2 then C + 1 else C);
      function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                            return Boolean
      is (C /= 2);
      Global_Flag : Boolean := True;
      function Convert (X : Boolean_Container) return B0.Boolean_Container
      is (B0.Booleans) with Global => (Input => Global_Flag);
      function Element (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean
      is (C /= 0);
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Convert);
      --  FAILS.

   end No_Globals_In_Model;

   package No_Globals_In_Contains is

      --  Model function not allowed to access global data.

      type Boolean_Container is (Booleans)
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (X : Boolean_Container) return Boolean_Cursor is (0);
      function Next (X : Boolean_Container; C : Boolean_Cursor)
                     return Boolean_Cursor
      is (if C /= 2 then C + 1 else C);
      function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                            return Boolean
      is (C /= 2);
      Global_Flag : Boolean := True;
      function Contains (X : Boolean_Container; Y : Boolean) return Boolean
      is (True) with Global => (Input => Global_Flag);
      function Element (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean
      is (C /= 0);
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
      --  FAILS.

   end No_Globals_In_Contains;

   package No_Dispatch_On_Model_Result is

      --  No dispatch on model result.

      package Non_Controlling is

         package Model_Declarator is
            type Model is tagged null record
              with Iterable => (First       => First,
                                Next        => Next,
                                Has_Element => Has_Element,
                                Element     => Element);
            function First (X : Model) return Boolean_Cursor is (0);
            function Next (X : Model; C : Boolean_Cursor)
                        return Boolean_Cursor
            is (if C /= 2 then C + 1 else C);
            function Has_Element (X : Model; C : Boolean_Cursor)
                               return Boolean
            is (C /= 2);
            function Element (X : Model; C : Boolean_Cursor)
                           return Boolean
            is (C /= 0);
         end Model_Declarator;
         use Model_Declarator;

         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Boolean_Container) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                     return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                            return Boolean
         is (C /= 2);
         function Model_F (X : Boolean_Container) return Model is (null record);
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Model_F);
         --  Fine.

      end Non_Controlling;


      package Controlling is

         type Model is tagged null record
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Model) return Boolean_Cursor is (0);
         function Next (X : Model; C : Boolean_Cursor)
                     return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Model; C : Boolean_Cursor)
                            return Boolean
         is (C /= 2);
         function Element (X : Model; C : Boolean_Cursor)
                        return Boolean
         is (C /= 0);

         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Boolean_Container) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                     return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                            return Boolean
         is (C /= 2);
         function Model_F (X : Boolean_Container) return Model is (null record);
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Model_F);
         --  FAILS

      end Controlling;

   end No_Dispatch_On_Model_Result;

   package Primitives is

     --  Contains and model function must be primitive of the container.

      package Contains_Primitive is

         type Tagged_Container is tagged null record
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         package Nested_Contains is
            type Tagged_Element is tagged null record;
            function Contains (X : Tagged_Container;
                               Y : Tagged_Element) return Boolean is (True);
         end Nested_Contains;
         function First (X : Tagged_Container) return Boolean is (True);
         function Next (X : Tagged_Container; C : Boolean) return Boolean
         is (False);
         function Has_Element (X : Tagged_Container; C : Boolean)
                               return Boolean
         is (C);
         function Element (X : Tagged_Container; C : Boolean)
                           return Nested_Contains.Tagged_Element
         is (null record);
         pragma Annotate (GNATprove, Iterable_For_Proof,
                          "Contains", Nested_Contains.Contains);
         --  FAILS

      end Contains_Primitive;

      package Model_Primitive is

         package B0 is new Make_Boolean_Container;
         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Boolean_Container) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                            return Boolean
         is (C /= 2);
         package Inner is
            function Model (X : Boolean_Container) return B0.Boolean_Container
            is (B0.Booleans);
         end Inner;
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                           return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Inner.Model);
         --  FAILS

      end Model_Primitive;

   end Primitives;

   package Volatility is

      package Model_Volatile is

         package B0 is new Make_Boolean_Container;
         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Boolean_Container) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                               return Boolean
         is (C /= 2);
         function Model (X : Boolean_Container) return B0.Boolean_Container
           with Volatile_Function, Import;
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                           return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove, Iterable_For_Proof, "Model", Model);
         --  FAILS

      end Model_Volatile;

      package Contains_Volatile is

         package B0 is new Make_Boolean_Container;
         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         function First (X : Boolean_Container) return Boolean_Cursor is (0);
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean_Cursor
         is (if C /= 2 then C + 1 else C);
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                               return Boolean
         is (C /= 2);
         function Contains (X : Boolean_Container; Y : Boolean) return Boolean
           with Import, Volatile_Function;
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                           return Boolean
         is (C /= 0);
         pragma Annotate (GNATprove,
                          Iterable_For_Proof,
                          "Contains",
                          Contains);
         --  FAILS

      end Contains_Volatile;

      package Primitives_Volatile is
         type Boolean_Container is (Booleans)
           with Iterable => (First       => First,
                             Next        => Next,
                             Has_Element => Has_Element,
                             Element     => Element);
         --  FAILS (error at every function)

         function First (X : Boolean_Container) return Boolean_Cursor
           with Import, Volatile_Function;
         function Next (X : Boolean_Container; C : Boolean_Cursor)
                        return Boolean_Cursor
           with Import, Volatile_Function;
         function Has_Element (X : Boolean_Container; C : Boolean_Cursor)
                               return Boolean
           with Import, Volatile_Function;
         function Element (X : Boolean_Container; C : Boolean_Cursor)
                           return Boolean
           with Import, Volatile_Function;

      end Primitives_Volatile;

   end Volatility;

begin
   null;
end Illegal_Errors;
