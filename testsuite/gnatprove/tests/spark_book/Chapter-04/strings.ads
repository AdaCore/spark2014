pragma SPARK_Mode(On);

package Strings is

   procedure Search (Text     : in  String;
                     Letter   : in  Character;
                     Start    : in  Positive;
                     Found    : out Boolean;
                     Position : out Positive)
      with
         Global  => null,
         Depends => (Found => (Text, Letter, Start),
                     Position => (Text, Letter, Start));

   procedure Get_Value (Text  : in     String;
                        Name  : in     String;
                        Value : in out Integer)
     with
        Global  => null,
        Depends => (Value => (Text, Name, Value));

end Strings;
