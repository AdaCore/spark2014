generic
package Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable with SPARK_Mode is

   type Mutable_T is new T with null record;

   procedure Initialize (This : in out Mutable_T;
                         Text : String) with
     Global => null,
     Pre'Class    => Text'Length <= Positive'Last,
     Post'Class   => (Text'Length = Length (This));

   procedure Append (This : in out Mutable_T;
                     Text : String) with
     Global => null;

end Aida.Strings.Generic_Immutable_Unbounded_String_Shared_Ptr.Mutable;
