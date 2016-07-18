generic
package Aida.Strings.Generic_Immutable_Unbounded_String.Mutable with SPARK_Mode is

   type Mutable_T is new T;

   procedure Initialize (This : in out Mutable_T;
                         Text : String) with
     Global => null,
     Pre    => Text'Length <= Positive'Last,
     Post   => (Text'Length = Length (This));

   procedure Append (This : in out Mutable_T;
                     Text : String) with
     Global => null;

end Aida.Strings.Generic_Immutable_Unbounded_String.Mutable;
