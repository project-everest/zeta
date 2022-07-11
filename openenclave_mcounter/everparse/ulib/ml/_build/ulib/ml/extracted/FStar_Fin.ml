open Prims
type 'n fin = Prims.int
type ('n, 'a) vect = 'a Prims.list
type ('n, 'a) seqn = 'a FStar_Seq_Base.seq
type ('a, 's) in_ = Prims.nat
let rec find :
  'a .
    'a FStar_Seq_Base.seq ->
      ('a -> Prims.bool) ->
        ('a, unit) in_ -> ('a, unit) in_ FStar_Pervasives_Native.option
  =
  fun s ->
    fun p ->
      fun i ->
        if p (FStar_Seq_Base.index s i)
        then FStar_Pervasives_Native.Some i
        else
          if (i + Prims.int_one) < (FStar_Seq_Base.length s)
          then find s p (i + Prims.int_one)
          else FStar_Pervasives_Native.None
let rec (pigeonhole :
  Prims.nat ->
    unit fin FStar_Seq_Base.seq ->
      ((unit fin, unit) in_ * (unit fin, unit) in_))
  =
  fun uu___1 ->
    fun uu___ ->
      (fun n ->
         fun s ->
           if n = Prims.int_zero
           then Obj.magic (Obj.repr (failwith "unreachable"))
           else
             Obj.magic
               (Obj.repr
                  (if n = Prims.int_one
                   then (Prims.int_zero, Prims.int_one)
                   else
                     (let k0 = FStar_Seq_Base.index s Prims.int_zero in
                      match find s (fun k -> k = k0) Prims.int_one with
                      | FStar_Pervasives_Native.Some i -> (Prims.int_zero, i)
                      | FStar_Pervasives_Native.None ->
                          let reduced_s =
                            FStar_Seq_Base.init n
                              (fun i ->
                                 let k =
                                   FStar_Seq_Base.index s (i + Prims.int_one) in
                                 if k < k0 then k else k - Prims.int_one) in
                          let uu___2 =
                            pigeonhole (n - Prims.int_one) reduced_s in
                          (match uu___2 with
                           | (i1, i2) ->
                               ((i1 + Prims.int_one), (i2 + Prims.int_one)))))))
        uu___1 uu___