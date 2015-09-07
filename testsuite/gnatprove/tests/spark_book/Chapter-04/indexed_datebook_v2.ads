with Dates;
package Indexed_Datebook_V2
  with
    SPARK_Mode     => On,
    Abstract_State => (Book, Index),
    Initializes    => Index
is
   type Status_Type is(Success, Description_Too_Long, Insufficient_Space);

   procedure Initialize
     with
       Global  => (Output => (Book, Index)),
       Depends => ((Book, Index) => null);

   procedure Compact_Index
     with
       Global  => (In_Out => Index),
       Depends => (Index =>+ null);

   procedure Add_Event (Description : in  String;
                        Date        : in  Dates.Datetime;
                        Status      : out Status_Type)
     with
       Global  => (In_Out => (Book, Index)),
       Depends => (Book   =>+ (Description, Date),
                   Index  =>+ (Description, Date),
                   Status =>  (Description, Book));

end Indexed_Datebook_V2;
