import LittlewoodInverse.EvenMomentCertificate

open scoped BigOperators
namespace LittlewoodInverse.MomentCertificate
open SincFormula
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem coefficient_le_5 : momentCoefficient 5 ≤ (605530070819498333084507 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 5)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_4, sincMoment_6]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_6 : momentCoefficient 6 ≤ (550000000000000000000000 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 6)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_6]

theorem coefficient_le_7 : momentCoefficient 7 ≤ (513469369729873615168791 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 7)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_6, sincMoment_8]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_8 : momentCoefficient 8 ≤ (479365079365079365079366 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 8)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_8]

theorem coefficient_le_9 : momentCoefficient 9 ≤ (454232592376835342069117 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 9)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_8, sincMoment_10]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_10 : momentCoefficient 10 ≤ (430417768959435626102293 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 10)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_10]

theorem coefficient_le_11 : momentCoefficient 11 ≤ (411767607879677092342742 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 11)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_10, sincMoment_12]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_12 : momentCoefficient 12 ≤ (393925565175565175565176 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 12)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_12]

theorem coefficient_le_13 : momentCoefficient 13 ≤ (379379659787849804235399 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 13)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_12, sincMoment_14]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_14 : momentCoefficient 14 ≤ (365370869485452818786153 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 14)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_14]

theorem coefficient_le_15 : momentCoefficient 15 ≤ (353616489808280089471048 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 15)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_14, sincMoment_16]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_16 : momentCoefficient 16 ≤ (342240261355340720420086 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 16)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_16]

theorem coefficient_le_17 : momentCoefficient 17 ≤ (332485818459256248555786 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 17)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_16, sincMoment_18]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_18 : momentCoefficient 18 ≤ (323009394156998706631060 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 18)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_18]

theorem coefficient_le_19 : momentCoefficient 19 ≤ (314745536877834806313489 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 19)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_18, sincMoment_20]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_20 : momentCoefficient 20 ≤ (306693101737982424530517 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 20)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_20]

theorem coefficient_le_21 : momentCoefficient 21 ≤ (299575298691184212434433 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 21)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_20, sincMoment_22]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_22 : momentCoefficient 22 ≤ (292622687231434779186401 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 22)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_22]

theorem coefficient_le_23 : momentCoefficient 23 ≤ (286408459234390315179995 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 23)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_22, sincMoment_24]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_24 : momentCoefficient 24 ≤ (280326198549807544976356 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 24)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_24]

theorem coefficient_le_25 : momentCoefficient 25 ≤ (274839286373083133780467 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 25)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_24, sincMoment_26]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_26 : momentCoefficient 26 ≤ (269459771240911935947803 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 26)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_26]

theorem coefficient_le_27 : momentCoefficient 27 ≤ (264568567340679437131269 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 27)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_26, sincMoment_28]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_28 : momentCoefficient 28 ≤ (259766148031495449005129 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 28)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_28]

theorem coefficient_le_29 : momentCoefficient 29 ≤ (255370134722379739202038 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 29)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_28, sincMoment_30]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_30 : momentCoefficient 30 ≤ (251048514990565639129980 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 30)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_30]

theorem coefficient_le_31 : momentCoefficient 31 ≤ (247069418691719419516841 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 31)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_30, sincMoment_32]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_32 : momentCoefficient 32 ≤ (243153390709991453691134 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 32)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_32]

theorem coefficient_le_33 : momentCoefficient 33 ≤ (239529229358052442814368 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 33)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_32, sincMoment_34]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_34 : momentCoefficient 34 ≤ (235959085535815717456299 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 34)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_34]

theorem coefficient_le_35 : momentCoefficient 35 ≤ (232640053628818441391740 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 35)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_34, sincMoment_36]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_36 : momentCoefficient 36 ≤ (229367707666440127178472 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 36)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_36]

theorem coefficient_le_37 : momentCoefficient 37 ≤ (226313264130048179780394 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 37)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_36, sincMoment_38]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_38 : momentCoefficient 38 ≤ (223299496002640021111360 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 38)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_38]

theorem coefficient_le_39 : momentCoefficient 39 ≤ (220476260331772005629706 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 39)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_38, sincMoment_40]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_40 : momentCoefficient 40 ≤ (217688719589893741822523 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 40)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_40]

theorem coefficient_le_41 : momentCoefficient 41 ≤ (215068923873437702484922 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 41)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_40, sincMoment_42]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_42 : momentCoefficient 42 ≤ (212480656339098271289704 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 42)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_42]

theorem coefficient_le_43 : momentCoefficient 43 ≤ (210040987543860965897637 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 43)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_42, sincMoment_44]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_44 : momentCoefficient 44 ≤ (207629330634190108790509 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 44)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_44]

theorem coefficient_le_45 : momentCoefficient 45 ≤ (205350051967607839082690 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 45)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_44, sincMoment_46]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_46 : momentCoefficient 46 ≤ (203095794386553654084526 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 46)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_46]

theorem coefficient_le_47 : momentCoefficient 47 ≤ (200960069570096998005355 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 47)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_46, sincMoment_48]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_48 : momentCoefficient 48 ≤ (198846803714474101112355 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 48)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_48]

theorem coefficient_le_49 : momentCoefficient 49 ≤ (196840171019595891366656 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 49)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_48, sincMoment_50]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_50 : momentCoefficient 50 ≤ (194853787957585484620895 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 50)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_50]

theorem coefficient_le_51 : momentCoefficient 51 ≤ (192963746296583987605020 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 51)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_50, sincMoment_52]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_52 : momentCoefficient 52 ≤ (191092037650905235475819 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 52)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_52]

theorem coefficient_le_53 : momentCoefficient 53 ≤ (189307717561325375025980 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 53)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_52, sincMoment_54]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_54 : momentCoefficient 54 ≤ (187540058543662569404965 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 54)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_54]

theorem coefficient_le_55 : momentCoefficient 55 ≤ (185851958228380312876920 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 55)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_54, sincMoment_56]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_56 : momentCoefficient 56 ≤ (184179052974337693311432 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 56)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_56]

theorem coefficient_le_57 : momentCoefficient 57 ≤ (182578824722731320442443 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 57)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_56, sincMoment_58]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_58 : momentCoefficient 58 ≤ (180992499954805016144850 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 58)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_58]

theorem coefficient_le_59 : momentCoefficient 59 ≤ (179472775961718972713112 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 59)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_58, sincMoment_60]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_60 : momentCoefficient 60 ≤ (177965812502996165883602 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 60)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_60]

theorem coefficient_le_61 : momentCoefficient 61 ≤ (176520061775326892295522 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 61)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_60, sincMoment_62]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_62 : momentCoefficient 62 ≤ (175086055972916907169592 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 62)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_62]

theorem coefficient_le_63 : momentCoefficient 63 ≤ (173708465972616269931717 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 63)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_62, sincMoment_64]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_64 : momentCoefficient 64 ≤ (172341714952029824569858 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 64)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_64]

theorem coefficient_le_65 : momentCoefficient 65 ≤ (171027093075874833634456 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 65)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_64, sincMoment_66]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_66 : momentCoefficient 66 ≤ (169722499129857048945914 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 66)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_66]

theorem coefficient_le_67 : momentCoefficient 67 ≤ (168466190213023576945493 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 67)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_66, sincMoment_68]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_68 : momentCoefficient 68 ≤ (167219180664880803419246 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 68)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_68]

theorem coefficient_le_69 : momentCoefficient 69 ≤ (166016997516742293542765 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 69)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_68, sincMoment_70]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_70 : momentCoefficient 70 ≤ (164823457182878568275823 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 70)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_70]

theorem coefficient_le_71 : momentCoefficient 71 ≤ (163671621789899381752419 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 71)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_70, sincMoment_72]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_72 : momentCoefficient 72 ≤ (162527835765591351422718 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 72)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_72]

theorem coefficient_le_73 : momentCoefficient 73 ≤ (161422929277999549608842 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 73)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_72, sincMoment_74]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_74 : momentCoefficient 74 ≤ (160325534232005254817514 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 74)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_74]

theorem coefficient_le_75 : momentCoefficient 75 ≤ (159264454224445661538512 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 75)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_74, sincMoment_76]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_76 : momentCoefficient 76 ≤ (158210396746315556408293 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 76)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_76]

theorem coefficient_le_77 : momentCoefficient 77 ≤ (157190320534406580790246 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 77)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_76, sincMoment_78]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_78 : momentCoefficient 78 ≤ (156176821358517374827753 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 78)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_78]

theorem coefficient_le_79 : momentCoefficient 79 ≤ (155195174382680054633774 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 79)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_78, sincMoment_80]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_80 : momentCoefficient 80 ≤ (154219697533605389306791 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 80)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_80]

theorem coefficient_le_81 : momentCoefficient 81 ≤ (153274126003195716019876 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 81)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_80, sincMoment_82]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_82 : momentCoefficient 82 ≤ (152334352081868543110602 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 82)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_82]

theorem coefficient_le_83 : momentCoefficient 83 ≤ (151422699217379853750460 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 83)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_82, sincMoment_84]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_84 : momentCoefficient 84 ≤ (150516502186942854657924 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 84)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_84]

theorem coefficient_le_85 : momentCoefficient 85 ≤ (149636787514047261998940 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 85)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_84, sincMoment_86]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_86 : momentCoefficient 86 ≤ (148762214456153767989599 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 86)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_86]

theorem coefficient_le_87 : momentCoefficient 87 ≤ (147912615698850146186390 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 87)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_86, sincMoment_88]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_88 : momentCoefficient 88 ≤ (147067869101424963187883 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 88)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_88]

theorem coefficient_le_89 : momentCoefficient 89 ≤ (146246706297326191577275 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 89)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_88, sincMoment_90]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_90 : momentCoefficient 90 ≤ (145430128507989348166008 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 90)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_90]

theorem coefficient_le_91 : momentCoefficient 91 ≤ (144635850030490379955137 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 91)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_90, sincMoment_92]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_92 : momentCoefficient 92 ≤ (143845909569510343865171 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 92)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_92]

theorem coefficient_le_93 : momentCoefficient 93 ≤ (143077079792083550172548 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 93)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_92, sincMoment_94]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_94 : momentCoefficient 94 ≤ (142312359267595732110256 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 94)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_94]

theorem coefficient_le_95 : momentCoefficient 95 ≤ (141567647646986865156731 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 95)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_94, sincMoment_96]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_96 : momentCoefficient 96 ≤ (140826833055425398483106 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 96)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_96]

theorem coefficient_le_97 : momentCoefficient 97 ≤ (140105004444819613872949 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 97)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_96, sincMoment_98]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_98 : momentCoefficient 98 ≤ (139386875672744487780133 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 98)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_98]

theorem coefficient_le_99 : momentCoefficient 99 ≤ (138686781704416091671003 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 99)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_98, sincMoment_100]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_100 : momentCoefficient 100 ≤ (137990204075500026911848 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 100)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_100]

theorem coefficient_le_101 : momentCoefficient 101 ≤ (137310775476145971299918 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 101)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_100, sincMoment_102]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_102 : momentCoefficient 102 ≤ (136634692210069107169388 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 102)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_102]

theorem coefficient_le_103 : momentCoefficient 103 ≤ (135974931931827058457670 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 103)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_102, sincMoment_104]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_104 : momentCoefficient 104 ≤ (135318357401052986607995 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 104)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_104]

theorem coefficient_le_105 : momentCoefficient 105 ≤ (134677334467818933084983 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 105)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_104, sincMoment_106]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_106 : momentCoefficient 106 ≤ (134039348154366733286429 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 106)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_106]

theorem coefficient_le_107 : momentCoefficient 107 ≤ (133416192137017109317040 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 107)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_106, sincMoment_108]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_108 : momentCoefficient 108 ≤ (132795933204943607634215 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 108)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_108]

theorem coefficient_le_109 : momentCoefficient 109 ≤ (132189829250887576196674 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 109)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_108, sincMoment_110]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_110 : momentCoefficient 110 ≤ (131586491661691193036716 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 110)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_110]

theorem coefficient_le_111 : momentCoefficient 111 ≤ (130996676014199271283668 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 111)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_110, sincMoment_112]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_112 : momentCoefficient 112 ≤ (130409504122108327319730 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 112)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_112]

theorem coefficient_le_113 : momentCoefficient 113 ≤ (129835260073384953756009 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 113)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_112, sincMoment_114]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_114 : momentCoefficient 114 ≤ (129263544645790186329268 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 114)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_114]

theorem coefficient_le_115 : momentCoefficient 115 ≤ (128704198875026441341443 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 115)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_114, sincMoment_116]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_116 : momentCoefficient 116 ≤ (128147273490398080560194 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 116)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_116]

theorem coefficient_le_117 : momentCoefficient 117 ≤ (127602192744258937516105 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 117)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_116, sincMoment_118]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_118 : momentCoefficient 118 ≤ (127059430525948900935386 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 118)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_118]

theorem coefficient_le_119 : momentCoefficient 119 ≤ (126528018604283935282193 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 119)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_118, sincMoment_120]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_120 : momentCoefficient 120 ≤ (125998829253815131084422 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 120)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_120]

theorem coefficient_le_121 : momentCoefficient 121 ≤ (125480524267970578266568 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 121)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_120, sincMoment_122]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_122 : momentCoefficient 122 ≤ (124964351365891741771177 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 122)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_122]

theorem coefficient_le_123 : momentCoefficient 123 ≤ (124458623240959754459005 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 123)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_122, sincMoment_124]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_124 : momentCoefficient 124 ≤ (123954941787206800947316 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 124)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_124]

theorem coefficient_le_125 : momentCoefficient 125 ≤ (123461289982970141991168 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 125)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_124, sincMoment_126]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_126 : momentCoefficient 126 ≤ (122969604152016294577955 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 126)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_126]

theorem coefficient_le_127 : momentCoefficient 127 ≤ (122487555580313242643426 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 127)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_126, sincMoment_128]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_128 : momentCoefficient 128 ≤ (122007396669287586182889 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 128)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_128]

theorem coefficient_le_129 : momentCoefficient 129 ≤ (121536503788099338790710 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 129)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_128, sincMoment_130]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_130 : momentCoefficient 130 ≤ (121067428338571852229992 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 130)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_130]

theorem coefficient_le_131 : momentCoefficient 131 ≤ (120607267405379339540534 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 131)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_130, sincMoment_132]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_132 : momentCoefficient 132 ≤ (120148855481704435821298 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 132)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_132]

theorem coefficient_le_133 : momentCoefficient 133 ≤ (119699024950620537168313 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 133)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_132, sincMoment_134]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_134 : momentCoefficient 134 ≤ (119250878559646704188036 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 134)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_134]

theorem coefficient_le_135 : momentCoefficient 135 ≤ (118810997608543389269967 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 135)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_134, sincMoment_136]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_136 : momentCoefficient 136 ≤ (118372739247172583322891 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 136)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_136]

theorem coefficient_le_137 : momentCoefficient 137 ≤ (117942446422524378885801 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 137)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_136, sincMoment_138]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_138 : momentCoefficient 138 ≤ (117513717741074357242275 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 138)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_138]

theorem coefficient_le_139 : momentCoefficient 139 ≤ (117092669709558567755744 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 139)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_138, sincMoment_140]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_140 : momentCoefficient 140 ≤ (116673130280172394634792 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 140)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_140]

theorem coefficient_le_141 : momentCoefficient 141 ≤ (116261000677227211415047 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 141)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_140, sincMoment_142]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_142 : momentCoefficient 142 ≤ (115850326857710619543148 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 142)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_142]

theorem coefficient_le_143 : momentCoefficient 143 ≤ (115446805224275580173850 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 143)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_142, sincMoment_144]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_144 : momentCoefficient 144 ≤ (115044689108745121881432 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 144)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_144]

theorem coefficient_le_145 : momentCoefficient 145 ≤ (114649479908312253798990 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 145)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_144, sincMoment_146]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_146 : momentCoefficient 146 ≤ (114255628356922699216980 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 146)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_146]

theorem coefficient_le_147 : momentCoefficient 147 ≤ (113868450065826471651399 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 147)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_146, sincMoment_148]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_148 : momentCoefficient 148 ≤ (113482583806629695911183 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 148)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_148]

theorem coefficient_le_149 : momentCoefficient 149 ≤ (113103168071212829085852 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 149)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_148, sincMoment_150]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_150 : momentCoefficient 150 ≤ (112725020867895365445850 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 150)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_150]

theorem coefficient_le_151 : momentCoefficient 151 ≤ (112353111722816990786156 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 151)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_150, sincMoment_152]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_152 : momentCoefficient 152 ≤ (111982429602680621000534 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 152)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_152]

theorem coefficient_le_153 : momentCoefficient 153 ≤ (111617782745193080509035 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 153)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_152, sincMoment_154]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_154 : momentCoefficient 154 ≤ (111254323282291881049291 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 154)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_154]

theorem coefficient_le_155 : momentCoefficient 155 ≤ (110896705397811101082696 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 155)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_154, sincMoment_156]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_156 : momentCoefficient 156 ≤ (110540237046647565827234 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 156)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_156]

theorem coefficient_le_157 : momentCoefficient 157 ≤ (110189425181386810569252 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 157)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_156, sincMoment_158]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_158 : momentCoefficient 158 ≤ (109839726657006225449314 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 158)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_158]

theorem coefficient_le_159 : momentCoefficient 159 ≤ (109495507633840529143179 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_neg (by decide : ¬Even 159)]
  norm_num only [Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat]
  rw [sincMoment_158, sincMoment_160]
  apply (Real.sqrt_le_iff).mpr
  constructor <;> norm_num

theorem coefficient_le_160 : momentCoefficient 160 ≤ (109152367334552935171958 : ℝ) / 1000000000000000000000000 := by
  rw [momentCoefficient, if_pos (by decide : Even 160)]
  norm_num only [Nat.cast_ofNat]
  norm_num [sincMoment_160]

end LittlewoodInverse.MomentCertificate
