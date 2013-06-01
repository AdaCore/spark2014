package A is
   type    Quarterly_Period_Type  is (Spring);
   type    Service_History_Type   is array (Quarterly_Period_Type range <>)
     of Integer;

  end A;
