// contains a model of full support structure made of steel of sbt
// No SBT (no LiSc, ribs, walls), only a steel housing made of straight beams
// around the He balloon, profiles approximated as solid rectangles:
//  - frames at the CAD z positions: vertical beams HEA260, horizontal IPE240
//  - longitudinal beams on top/bottom at the former longitudinal rib
//    positions: IPE240, last segment HEA260
//  - corner beams: top IPE240, bottom HEA260 (between frames 2-5 IPE270)
//  longitudinal and corner beams run tilted from frame to frame along the
//  slope of the vessel


// SPDX-License-Identifier: LGPL-3.0-or-later
// SPDX-FileCopyrightText: Copyright CERN for the benefit of the SHiP
// Collaboration

// 09/07/2024
// SBT software contact: anupama.reghunath@cern.ch
/**
 * @file veto_fullsupport.cxx
 * @brief Implementation of the Veto detector class.
 *
 * This file contains the definitions for the Veto class used in the
 * FairShip Software. The class is responsible for simulating the Decay
 * Vessel(helium) + integrated SBT geometry and interactions.
 */

#include "veto.h"

#include <cmath>
#include <iostream>
#include <vector>

#include "FairGeoBuilder.h"
#include "FairGeoInterface.h"
#include "FairGeoLoader.h"
#include "FairGeoMedia.h"
#include "FairGeoNode.h"
#include "FairGeoVolume.h"
#include "FairLogger.h"  /// for FairLogger, MESSAGE_ORIGIN
#include "FairRootManager.h"
#include "FairRun.h"
#include "FairRuntimeDb.h"
#include "FairVolume.h"
#include "ShipDetectorList.h"
#include "ShipGeoUtil.h"
#include "ShipStack.h"
#include "TClonesArray.h"
#include "TGeoArb8.h"
#include "TGeoBBox.h"
#include "TGeoBoolNode.h"
#include "TGeoCompositeShape.h"
#include "TGeoCone.h"
#include "TGeoEltu.h"
#include "TGeoManager.h"
#include "TGeoMaterial.h"
#include "TGeoShapeAssembly.h"
#include "TGeoSphere.h"
#include "TGeoTube.h"
#include "TMath.h"
#include "TParticle.h"
#include "TVirtualMC.h"
#include "vetoPoint.h"

#include "ShipUnit.h"
using ShipUnit::cm;
using ShipUnit::m;
using ShipUnit::mm;


/// steel beam profiles, approximated as solid rectangles with the same
// cross-section area incl. fillets (see beam_profiles.py):
// height h (away from the vessel) x thickness t
struct BeamProfile {
  double h;
  double t;
  int color;
};
constexpr BeamProfile kIPE240{240 * mm, 16.3 * mm, kCyan + 2};
constexpr BeamProfile kIPE270{270 * mm, 17.0 * mm, kOrange};
constexpr BeamProfile kHEA260{250 * mm, 34.7 * mm, kMagenta};

/**
 * @brief Constructor for the Veto class.
 *
 * Initializes the veto detector with the given parameters.
 *
 */
veto::veto()
    : SHiP::Detector<vetoPoint>("Veto", kTRUE, kVETO),
      fFastMuon(kFALSE),
      fFollowMuon(kFALSE) {
  fUseSupport = 1;
  fLiquidVeto = 1;
}

TGeoVolume* veto::make_geo_trapezoid(
    const TString& xname, Double_t z_thick, Double_t x_thick_start,
    Double_t x_thick_end, Double_t y_thick_start, Double_t y_thick_end,
    Int_t color, TGeoMedium* material, Bool_t sens = kFALSE) {
  Double_t dz = z_thick / 2;
  Double_t dx1 = x_thick_start / 2 - 1.E-6;
  Double_t dx2 = x_thick_end / 2 - 1.E-6;
  Double_t dy1 = y_thick_start / 2 - 1.E-6;
  Double_t dy2 = y_thick_end / 2 - 1.E-6;
  TGeoArb8* T1 = new TGeoArb8("T1" + xname, dz + 1.E-6);
  T1->SetVertex(0, -dx1, -dy1);
  T1->SetVertex(1, -dx1, dy1);
  T1->SetVertex(2, dx1, dy1);
  T1->SetVertex(3, dx1, -dy1);
  T1->SetVertex(4, -dx2, -dy2);
  T1->SetVertex(5, -dx2, dy2);
  T1->SetVertex(6, dx2, dy2);
  T1->SetVertex(7, dx2, -dy2);

  TGeoVolume* T = new TGeoVolume(xname, T1, material);
  T->SetLineColor(color);
  if (sens) {
    AddSensitiveVolume(T);
  }  // and make the volumes sensitive..
  return T;
}

double veto::wx(double z) {  // calculate x thickness at z

  double wx1 = VetoStartInnerX;
  double wx2 = VetoEndInnerX;
  double z1 = 0 * m;
  double z2 = 50 * m;

  return (wx1 + (z - z1) * (wx2 - wx1) / (z2 - z1));
}

double veto::wy(double z) {  // calculate y thickness at z

  double wy1 = VetoStartInnerY;
  double wy2 = VetoEndInnerY;
  double z1 = 0 * m;
  double z2 = 50 * m;

  return (wy1 + (z - z1) * (wy2 - wy1) / (z2 - z1));
}

namespace {
/// straight steel beam (box) with half lengths dx, dy, dz
TGeoVolume* make_beam(const TString& xname, double dx, double dy, double dz,
                      Int_t color, TGeoMedium* material) {
  TGeoVolume* T = new TGeoVolume(
      xname, new TGeoBBox(xname + "_shape", dx, dy, dz), material);
  T->SetLineColor(color);
  return T;
}

/// straight steel beam with cross section 2*hx x 2*hy, centred at the origin;
/// the cross section centre is shifted by (-sx, -sy) at -dz and (sx, sy) at +dz
TGeoVolume* make_tilted_beam(const TString& xname, double hx, double hy,
                             double dz, double sx, double sy, Int_t color,
                             TGeoMedium* material) {
  TGeoArb8* shape = new TGeoArb8(xname + "_shape", dz);
  shape->SetVertex(0, -sx - hx, -sy - hy);
  shape->SetVertex(1, -sx - hx, -sy + hy);
  shape->SetVertex(2, -sx + hx, -sy + hy);
  shape->SetVertex(3, -sx + hx, -sy - hy);
  shape->SetVertex(4, sx - hx, sy - hy);
  shape->SetVertex(5, sx - hx, sy + hy);
  shape->SetVertex(6, sx + hx, sy + hy);
  shape->SetVertex(7, sx + hx, sy - hy);
  TGeoVolume* T = new TGeoVolume(xname, shape, material);
  T->SetLineColor(color);
  return T;
}
}  // namespace

TGeoVolume* veto::make_segments() {
  TGeoVolumeAssembly* tTankVol = new TGeoVolumeAssembly("T2");

  int nx = 2;  // number of longitudinal beams on top and on bottom

  // wall, scintillator and rib dimensions of the former SBT are only used as
  // reference coordinates for placing the steel beams
  double wall_thickness = 6 * mm;  // fixed here, ignores innerSupport in yaml
  double lisc_thickness = f_VetoThickness;
  double rib_thickness = 6 * mm;   // fixed here, ignores rib in yaml


  const double z_start = 0 * m;
  const double z_end = 50 * m;

  /// z positions of the steel frames (upstream face) from CAD, given relative
  /// to the vessel centre and shifted to the local frame z = 0 ... 50 m
  const double z_offset = 25 * m;
  std::vector<double> z_frames;
  for (double z : {-25.0, -20.0, -15.01, -10.01, -5.02, -0.02, 4.97, 9.97,
                   14.96, 19.96, 25.0}) {
    z_frames.push_back(z_offset + z * m);
  }

  TGeoMedium* steelMed = gGeoManager->GetMedium("steel");

  TGeoVolumeAssembly* frames = new TGeoVolumeAssembly("VetoSteelFrame");
  TGeoVolumeAssembly* longit_beams =
      new TGeoVolumeAssembly("VetoSteelLongitBeam");
  TGeoVolumeAssembly* corner_beams =
      new TGeoVolumeAssembly("VetoSteelCornerBeam");

  TString name("");
  /// steel frames: vertical beams (along y, HEA260) over the full outer
  /// height, horizontal beams (along x, IPE240) in between; inner edge at the
  /// former inner wall, all members start at the upstream face zf
  for (size_t k = 0; k < z_frames.size(); ++k) {
    const double zf = z_frames[k];
    const double zc = zf + kHEA260.t / 2;
    const double ax = wx(zc) / 2 + wall_thickness;  // inner half width
    const double ay = wy(zc) / 2 + wall_thickness;  // inner half height

    const double xs = ax + kHEA260.h / 2;
    const double yt = ay + kIPE240.h / 2;
    const double zs = zf + kHEA260.t / 2;
    const double zt = zf + kIPE240.t / 2;
    for (int xsign : {1, -1}) {
      name.Form("SteelFrameSide_F%02zu_%s", k, xsign > 0 ? "R" : "L");
      TGeoVolume* side = make_beam(name, kHEA260.h / 2, ay + kHEA260.h,
                                   kHEA260.t / 2, kHEA260.color, steelMed);
      frames->AddNode(side, 1, new TGeoTranslation(xsign * xs, 0, zs));
    }
    for (int ysign : {1, -1}) {
      name.Form("SteelFrame%s_F%02zu", ysign > 0 ? "Top" : "Bottom", k);
      TGeoVolume* topbottom = make_beam(name, ax, kIPE240.h / 2,
                                        kIPE240.t / 2, kIPE240.color, steelMed);
      frames->AddNode(topbottom, 1, new TGeoTranslation(0, ysign * yt, zt));
    }
  }

  /// longitudinal and corner beams: one straight piece from frame to frame,
  /// following the slope of the vessel in x and y
  auto x_longit = [&](double z, int j, int n) {  // n beams, evenly spaced
    const double x_width = wx(z) + 2 * (wall_thickness + lisc_thickness);
    const double x_step = (x_width - n * rib_thickness) / (n + 1);
    return x_width / 2 - (j + 1) * x_step - j * rib_thickness -
           rib_thickness / 2;
  };
  auto x_corner = [&](double z) {
    return wx(z) / 2 + wall_thickness + lisc_thickness / 2;
  };
  // one tilted beam from zb1 to zb2; x1/x2 = x centre at zb1/zb2,
  // ysign = +1 top, -1 bottom; inner edge at the former inner wall
  auto place_beam = [&](TGeoVolumeAssembly* assembly, const TString& nm,
                        const BeamProfile& p, double zb1, double zb2,
                        double x1, double x2, int ysign) {
    const double y1 = ysign * (wy(zb1) / 2 + wall_thickness + p.h / 2);
    const double y2 = ysign * (wy(zb2) / 2 + wall_thickness + p.h / 2);
    TGeoVolume* v = make_tilted_beam(nm, p.t / 2, p.h / 2, (zb2 - zb1) / 2,
                                     (x2 - x1) / 2, (y2 - y1) / 2, p.color,
                                     steelMed);
    assembly->AddNode(v, 1, new TGeoTranslation((x1 + x2) / 2, (y1 + y2) / 2,
                                                (zb1 + zb2) / 2));
  };

  /// profiles per segment k (between frame k and k + 1, counted from 0)
  const size_t nSeg = z_frames.size() - 1;
  auto corner_profile = [&](size_t k, int ysign) -> const BeamProfile& {
    if (ysign > 0) return kIPE240;                  // top corners
    return (k >= 1 && k <= 3) ? kIPE270 : kHEA260;  // frames 2-5: IPE270
  };
  auto middle_profile = [&](size_t k) -> const BeamProfile& {
    return (k + 1 == nSeg) ? kHEA260 : kIPE240;  // last segment: HEA260
  };

  for (size_t k = 0; k < nSeg; ++k) {
    const double zb1 = z_frames[k] + kHEA260.t;  // behind the thickest member
    const double zb2 = z_frames[k + 1];
    for (int ysign : {1, -1}) {
      const char* tb = ysign > 0 ? "top" : "bottom";
      // first 5 segments: one centred beam, afterwards nx
      const int n_mid = (k < 5) ? 1 : nx;
      for (int j = 0; j < n_mid; ++j) {
        name.Form("SteelLongitBeam_S%02zu_%s_%d", k, tb, j);
        place_beam(longit_beams, name, middle_profile(k), zb1, zb2,
                   x_longit(zb1, j, n_mid), x_longit(zb2, j, n_mid), ysign);

      }
      for (int xsign : {1, -1}) {
        name.Form("SteelCornerBeam_S%02zu_%s_%s", k, tb,
                  xsign > 0 ? "R" : "L");
        place_beam(corner_beams, name, corner_profile(k, ysign), zb1, zb2,
                   xsign * x_corner(zb1), xsign * x_corner(zb2), ysign);
      }
    }
  }


  /// decay medium nested in the He balloon (no inner wall)
  const double balloon_thickness = f_he_balloon_thickness;
  TGeoVolume* vessel = nullptr;  // balloon (or decay medium)
  TGeoVolume* decay_medium = nullptr;
  if (balloon_thickness > 0) {
    vessel =
        make_geo_trapezoid("HeBalloon", z_end - z_start, wx(z_start), wx(z_end),
                           wy(z_start), wy(z_end), kGreen, f_he_balloon_med);
    decay_medium = make_geo_trapezoid(
        "decay_medium", (z_end - z_start) - 2 * balloon_thickness,
        wx(z_start + balloon_thickness) - 2 * balloon_thickness,
        wx(z_end - balloon_thickness) - 2 * balloon_thickness,
        wy(z_start + balloon_thickness) - 2 * balloon_thickness,
        wy(z_end - balloon_thickness) - 2 * balloon_thickness, 1,
        decayVolumeMed);
    vessel->AddNode(decay_medium, 0);
  } else {
    decay_medium = make_geo_trapezoid("decay_medium", z_end - z_start,
                                      wx(z_start), wx(z_end), wy(z_start),
                                      wy(z_end), 1, decayVolumeMed);
    vessel = decay_medium;
  }
  decay_medium->SetVisibility(kFALSE);
  tTankVol->AddNode(vessel, 0,
                    new TGeoTranslation(0, 0, (z_start + z_end) / 2));

  tTankVol->AddNode(frames, 0, new TGeoTranslation(0, 0, 0));
  tTankVol->AddNode(longit_beams, 0, new TGeoTranslation(0, 0, 0));
  tTankVol->AddNode(corner_beams, 0, new TGeoTranslation(0, 0, 0));

  return tTankVol;
}

// -------------------------------------------------------------------------
/**
 * @brief Processes a hit in the veto detector.
 *
 * This method is called whenever a hit is registered in the veto detector.
 * It processes the hit information and records the relevant data.
 *
 * @param x X-coordinate of the hit.
 * @param y Y-coordinate of the hit.
 * @param z Z-coordinate of the hit.
 * @param time Time of the hit.
 * @param energy Energy deposited by the hit.
 * @return True if the hit was processed successfully, false otherwise.
 */
Bool_t veto::ProcessHits(FairVolume* vol) {
  /** This method is called from the MC stepping */
  // Set parameters at entrance of volume. Reset ELoss.
  if (gMC->IsTrackEntering()) {
    fELoss = 0.;
    fTime = gMC->TrackTime() * 1.0e09;
    fLength = gMC->TrackLength();
    gMC->TrackPosition(fPos);
    gMC->TrackMomentum(fMom);
  }
  // Sum energy loss for all steps in the active volume
  fELoss += gMC->Edep();

  // Create vetoPoint at exit of active volume
  if (gMC->IsTrackExiting() || gMC->IsTrackStop() ||
      gMC->IsTrackDisappeared()) {
    if (fELoss == 0.) {
      return kFALSE;
    }

    fTrackID = gMC->GetStack()->GetCurrentTrackNumber();
    fEventID = gMC->CurrentEvent();
    Int_t veto_uniqueId;
    gMC->CurrentVolID(veto_uniqueId);
    TParticle* p = gMC->GetStack()->GetCurrentTrack();
    Int_t pdgCode = p->GetPdgCode();
    TLorentzVector pos;
    gMC->TrackPosition(pos);
    TLorentzVector Mom;
    gMC->TrackMomentum(Mom);
    Double_t xmean = (fPos.X() + pos.X()) / 2.;
    Double_t ymean = (fPos.Y() + pos.Y()) / 2.;
    Double_t zmean = (fPos.Z() + pos.Z()) / 2.;
    AddHit(fEventID, fTrackID, veto_uniqueId, TVector3(xmean, ymean, zmean),
           TVector3(fMom.Px(), fMom.Py(), fMom.Pz()), fTime, fLength, fELoss,
           pdgCode, TVector3(pos.X(), pos.Y(), pos.Z()),
           TVector3(Mom.Px(), Mom.Py(), Mom.Pz()));

    // Increment number of veto det points in TParticle
    ShipStack* stack = dynamic_cast<ShipStack*>(gMC->GetStack());
    stack->AddPoint(kVETO);
  }

  return kTRUE;
}

void veto::PreTrack() {
  if (!fFastMuon) {
    return;
  }
  if (TMath::Abs(gMC->TrackPid()) != 13) {
    gMC->StopTrack();
  }
}

/**
 * @brief Constructs the detector geometry.
 *
 * This function is responsible for setting up the geometry of the
 * DecayVolume+SBT detector. It is called during the detector's construction
 * phase.
 */

void veto::ConstructGeometry() {
  TGeoVolume* top = gGeoManager->GetTopVolume();

  ShipGeo::InitMedium(supportMedOut_name.Data());
  ShipGeo::InitMedium(supportMedIn_name.Data());
  ShipGeo::InitMedium(vetoMed_name.Data());
  ShipGeo::InitMedium(decayVolumeMed_name.Data());
  ShipGeo::InitMedium(f_he_balloon_med_name.Data());
  ShipGeo::InitMedium("steel");

  gGeoManager->SetNsegments(100);

  vetoMed = gGeoManager->GetMedium(
      vetoMed_name);  //! medium of veto counter, liquid or plastic scintillator
  supportMedIn = gGeoManager->GetMedium(
      supportMedIn_name);  //! medium of support structure, iron, balloon
  supportMedOut = gGeoManager->GetMedium(
      supportMedOut_name);  //! medium of support structure, aluminium, balloon
  decayVolumeMed = gGeoManager->GetMedium(
      decayVolumeMed_name);  // decay volume, air/helium/vacuum
  f_he_balloon_med =
      gGeoManager->GetMedium(f_he_balloon_med_name);  // He Balloon medium, pvc
  LOG(info) << "veto: Decay Volume medium set as: " << decayVolumeMed_name;
  TGeoVolume* tDecayVol = new TGeoVolumeAssembly("DecayVolume");

  TGeoVolume* seg = make_segments();
  tDecayVol->AddNode(seg, 1, new TGeoTranslation(0, 0, 0));
  top->AddNode(tDecayVol, 1, new TGeoTranslation(0, 0, zStartDecayVol));  //));

  // only for fastMuon simulation, otherwise output becomes too big
  if (fFastMuon && fFollowMuon) {
    const char* Vol = "TGeoVolume";
    const char* Cavern = "Cavern";
    const char* Ain = "AbsorberAdd";
    const char* Aout = "AbsorberAddCore";
    TObjArray* volumelist = gGeoManager->GetListOfVolumes();
    int lastvolume = volumelist->GetLast();
    int volumeiterator = 0;
    while (volumeiterator <= lastvolume) {
      const char* volumename = volumelist->At(volumeiterator)->GetName();
      const char* classname = volumelist->At(volumeiterator)->ClassName();
      if (strstr(classname, Vol)) {
        if (strstr(volumename, Cavern) || strstr(volumename, Ain) ||
            strstr(volumename, Aout)) {
          AddSensitiveVolume(gGeoManager->GetVolume(volumename));
          LOG(info) << "veto: made sensitive for following muons: "
                    << volumename;
        }
      }
      volumeiterator++;
    }
  }
}
