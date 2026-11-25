module

public import RKCert.ReviewedNative.NativePencilCubicDAGPart036

@[expose] public section
namespace RKResearch.Certified.Graded.NativePencilCubicDAG
open NativeHornerWitness NativeHornerCheckpoints

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

theorem e5400 : o1.scale b334 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5401 : o1.scale b334 b63=b5467 := @scale_cons V1 _ o1 b334 b62 b5411 (List.nil : V2) (List.nil : V2) b5467 e5399 e5400 (by rfl)
theorem e5402 : o1.add b5411 (List.nil : V1)=b5411 := by rfl
theorem e5403 : o2.add (List.nil : V2) b5466=b5466 := by rfl
theorem e5404 : o2.add b5467 b5468=b5464 := @add_cons V1 _ o1 b5411 (List.nil : V1) b5411 (List.nil : V2) b5466 b5466 b5464 e5402 e5403 (by rfl)
theorem e5405 : o2.mul b5463 b63=b5464 := @mul_cons V1 _ o1 b334 b5465 b63 b5466 b5467 b5468 b5464 e5398 e5401 (by rfl) e5404
theorem e5406 : o1.mul b333 b62=b5410 := by decide
theorem e5407 : o1.scale b333 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5408 : o1.scale b333 b63=b5469 := @scale_cons V1 _ o1 b333 b62 b5410 (List.nil : V2) (List.nil : V2) b5469 e5406 e5407 (by rfl)
theorem e5409 : o1.add b5410 (List.nil : V1)=b5410 := by rfl
theorem e5410 : o2.add (List.nil : V2) b5464=b5464 := by rfl
theorem e5411 : o2.add b5469 b5470=b5462 := @add_cons V1 _ o1 b5410 (List.nil : V1) b5410 (List.nil : V2) b5464 b5464 b5462 e5409 e5410 (by rfl)
theorem e5412 : o2.mul b5461 b63=b5462 := @mul_cons V1 _ o1 b333 b5463 b63 b5464 b5469 b5470 b5462 e5405 e5408 (by rfl) e5411
theorem e5413 : o1.mul b332 b62=b5409 := by decide
theorem e5414 : o1.scale b332 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5415 : o1.scale b332 b63=b5471 := @scale_cons V1 _ o1 b332 b62 b5409 (List.nil : V2) (List.nil : V2) b5471 e5413 e5414 (by rfl)
theorem e5416 : o1.add b5409 (List.nil : V1)=b5409 := by rfl
theorem e5417 : o2.add (List.nil : V2) b5462=b5462 := by rfl
theorem e5418 : o2.add b5471 b5472=b5460 := @add_cons V1 _ o1 b5409 (List.nil : V1) b5409 (List.nil : V2) b5462 b5462 b5460 e5416 e5417 (by rfl)
theorem e5419 : o2.mul b5459 b63=b5460 := @mul_cons V1 _ o1 b332 b5461 b63 b5462 b5471 b5472 b5460 e5412 e5415 (by rfl) e5418
theorem e5420 : o1.mul b331 b62=b5408 := by decide
theorem e5421 : o1.scale b331 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5422 : o1.scale b331 b63=b5473 := @scale_cons V1 _ o1 b331 b62 b5408 (List.nil : V2) (List.nil : V2) b5473 e5420 e5421 (by rfl)
theorem e5423 : o1.add b5408 (List.nil : V1)=b5408 := by rfl
theorem e5424 : o2.add (List.nil : V2) b5460=b5460 := by rfl
theorem e5425 : o2.add b5473 b5474=b5458 := @add_cons V1 _ o1 b5408 (List.nil : V1) b5408 (List.nil : V2) b5460 b5460 b5458 e5423 e5424 (by rfl)
theorem e5426 : o2.mul b5457 b63=b5458 := @mul_cons V1 _ o1 b331 b5459 b63 b5460 b5473 b5474 b5458 e5419 e5422 (by rfl) e5425
theorem e5427 : o1.mul b330 b62=b5407 := by decide
theorem e5428 : o1.scale b330 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5429 : o1.scale b330 b63=b5475 := @scale_cons V1 _ o1 b330 b62 b5407 (List.nil : V2) (List.nil : V2) b5475 e5427 e5428 (by rfl)
theorem e5430 : o1.add b5407 (List.nil : V1)=b5407 := by rfl
theorem e5431 : o2.add (List.nil : V2) b5458=b5458 := by rfl
theorem e5432 : o2.add b5475 b5476=b5456 := @add_cons V1 _ o1 b5407 (List.nil : V1) b5407 (List.nil : V2) b5458 b5458 b5456 e5430 e5431 (by rfl)
theorem e5433 : o2.mul b5455 b63=b5456 := @mul_cons V1 _ o1 b330 b5457 b63 b5458 b5475 b5476 b5456 e5426 e5429 (by rfl) e5432
theorem e5434 : o1.mul b329 b62=b5406 := by decide
theorem e5435 : o1.scale b329 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5436 : o1.scale b329 b63=b5477 := @scale_cons V1 _ o1 b329 b62 b5406 (List.nil : V2) (List.nil : V2) b5477 e5434 e5435 (by rfl)
theorem e5437 : o1.add b5406 (List.nil : V1)=b5406 := by rfl
theorem e5438 : o2.add (List.nil : V2) b5456=b5456 := by rfl
theorem e5439 : o2.add b5477 b5478=b5454 := @add_cons V1 _ o1 b5406 (List.nil : V1) b5406 (List.nil : V2) b5456 b5456 b5454 e5437 e5438 (by rfl)
theorem e5440 : o2.mul b5453 b63=b5454 := @mul_cons V1 _ o1 b329 b5455 b63 b5456 b5477 b5478 b5454 e5433 e5436 (by rfl) e5439
theorem e5441 : o1.mul b328 b62=b5405 := by decide
theorem e5442 : o1.scale b328 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5443 : o1.scale b328 b63=b5479 := @scale_cons V1 _ o1 b328 b62 b5405 (List.nil : V2) (List.nil : V2) b5479 e5441 e5442 (by rfl)
theorem e5444 : o1.add b5405 (List.nil : V1)=b5405 := by rfl
theorem e5445 : o2.add (List.nil : V2) b5454=b5454 := by rfl
theorem e5446 : o2.add b5479 b5480=b5452 := @add_cons V1 _ o1 b5405 (List.nil : V1) b5405 (List.nil : V2) b5454 b5454 b5452 e5444 e5445 (by rfl)
theorem e5447 : o2.mul b5451 b63=b5452 := @mul_cons V1 _ o1 b328 b5453 b63 b5454 b5479 b5480 b5452 e5440 e5443 (by rfl) e5446
theorem e5448 : o1.mul b327 b62=b5404 := by decide
theorem e5449 : o1.scale b327 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5450 : o1.scale b327 b63=b5481 := @scale_cons V1 _ o1 b327 b62 b5404 (List.nil : V2) (List.nil : V2) b5481 e5448 e5449 (by rfl)
theorem e5451 : o1.add b5404 (List.nil : V1)=b5404 := by rfl
theorem e5452 : o2.add (List.nil : V2) b5452=b5452 := by rfl
theorem e5453 : o2.add b5481 b5482=b5450 := @add_cons V1 _ o1 b5404 (List.nil : V1) b5404 (List.nil : V2) b5452 b5452 b5450 e5451 e5452 (by rfl)
theorem e5454 : o2.mul b5449 b63=b5450 := @mul_cons V1 _ o1 b327 b5451 b63 b5452 b5481 b5482 b5450 e5447 e5450 (by rfl) e5453
theorem e5455 : o1.mul b326 b62=b5403 := by decide
theorem e5456 : o1.scale b326 (List.nil : V2)=(List.nil : V2) := by rfl
theorem e5457 : o1.scale b326 b63=b5483 := @scale_cons V1 _ o1 b326 b62 b5403 (List.nil : V2) (List.nil : V2) b5483 e5455 e5456 (by rfl)
theorem e5458 : o1.add b5403 (List.nil : V1)=b5403 := by rfl
theorem e5459 : o2.add (List.nil : V2) b5450=b5450 := by rfl
theorem e5460 : o2.add b5483 b5484=b5448 := @add_cons V1 _ o1 b5403 (List.nil : V1) b5403 (List.nil : V2) b5450 b5450 b5448 e5458 e5459 (by rfl)
theorem e5461 : o2.mul b5447 b63=b5448 := @mul_cons V1 _ o1 b326 b5449 b63 b5450 b5483 b5484 b5448 e5454 e5457 (by rfl) e5460
theorem e5462 : o1.mul (List.nil : V1) b62=(List.nil : V1) := by rfl
theorem e5463 : o1.scale (List.nil : V1) b63=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b62 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) e5462 e3696 (by rfl)
theorem e5464 : o2.add (List.nil : V2) b5446=b5446 := by rfl
theorem e5465 : o2.mul b5445 b63=b5446 := @mul_cons V1 _ o1 (List.nil : V1) b5447 b63 b5448 (List.nil : V2) b5446 b5446 e5461 e5463 (by rfl) e5464
theorem e5466 : o2.add (List.nil : V2) b5444=b5444 := by rfl
theorem e5467 : o2.mul b5443 b63=b5444 := @mul_cons V1 _ o1 (List.nil : V1) b5445 b63 b5446 (List.nil : V2) b5444 b5444 e5465 e5463 (by rfl) e5466
theorem e5468 : o2.add (List.nil : V2) b5442=b5442 := by rfl
theorem e5469 : o2.mul b5441 b63=b5442 := @mul_cons V1 _ o1 (List.nil : V1) b5443 b63 b5444 (List.nil : V2) b5442 b5442 e5467 e5463 (by rfl) e5468
theorem e5470 : o2.add (List.nil : V2) b5440=b5440 := by rfl
theorem e5471 : o2.mul b5439 b63=b5440 := @mul_cons V1 _ o1 (List.nil : V1) b5441 b63 b5442 (List.nil : V2) b5440 b5440 e5469 e5463 (by rfl) e5470
theorem e5472 : o2.add (List.nil : V2) b5438=b5438 := by rfl
theorem e5473 : o2.mul b5437 b63=b5438 := @mul_cons V1 _ o1 (List.nil : V1) b5439 b63 b5440 (List.nil : V2) b5438 b5438 e5471 e5463 (by rfl) e5472
theorem e5474 : o2.add (List.nil : V2) b5413=b5413 := by rfl
theorem e5475 : o2.mul b336 b63=b5413 := @mul_cons V1 _ o1 (List.nil : V1) b5437 b63 b5438 (List.nil : V2) b5413 b5413 e5473 e5463 (by rfl) e5474
theorem e5476 : o2.mul (List.nil : V2) b65=(List.nil : V2) := by rfl
theorem e5477 : o1.mul b335 b64=b5423 := by decide
theorem e5478 : o1.scale b335 b65=b5501 := @scale_cons V1 _ o1 b335 b64 b5423 (List.nil : V2) (List.nil : V2) b5501 e5477 e5395 (by rfl)
theorem e5479 : o2.add b5501 (List.nil : V2)=b5501 := by rfl
theorem e5480 : o2.mul b5465 b65=b5501 := @mul_cons V1 _ o1 b335 (List.nil : V2) b65 (List.nil : V2) b5501 (List.nil : V2) b5501 e5476 e5478 (by rfl) e5479
theorem e5481 : o1.mul b334 b64=b5422 := by decide
theorem e5482 : o1.scale b334 b65=b5502 := @scale_cons V1 _ o1 b334 b64 b5422 (List.nil : V2) (List.nil : V2) b5502 e5481 e5400 (by rfl)
theorem e5483 : o1.add b5422 (List.nil : V1)=b5422 := by rfl
theorem e5484 : o2.add (List.nil : V2) b5501=b5501 := by rfl
theorem e5485 : o2.add b5502 b5503=b5500 := @add_cons V1 _ o1 b5422 (List.nil : V1) b5422 (List.nil : V2) b5501 b5501 b5500 e5483 e5484 (by rfl)
theorem e5486 : o2.mul b5463 b65=b5500 := @mul_cons V1 _ o1 b334 b5465 b65 b5501 b5502 b5503 b5500 e5480 e5482 (by rfl) e5485
theorem e5487 : o1.mul b333 b64=b5421 := by decide
theorem e5488 : o1.scale b333 b65=b5504 := @scale_cons V1 _ o1 b333 b64 b5421 (List.nil : V2) (List.nil : V2) b5504 e5487 e5407 (by rfl)
theorem e5489 : o1.add b5421 (List.nil : V1)=b5421 := by rfl
theorem e5490 : o2.add (List.nil : V2) b5500=b5500 := by rfl
theorem e5491 : o2.add b5504 b5505=b5499 := @add_cons V1 _ o1 b5421 (List.nil : V1) b5421 (List.nil : V2) b5500 b5500 b5499 e5489 e5490 (by rfl)
theorem e5492 : o2.mul b5461 b65=b5499 := @mul_cons V1 _ o1 b333 b5463 b65 b5500 b5504 b5505 b5499 e5486 e5488 (by rfl) e5491
theorem e5493 : o1.mul b332 b64=b5420 := by decide
theorem e5494 : o1.scale b332 b65=b5506 := @scale_cons V1 _ o1 b332 b64 b5420 (List.nil : V2) (List.nil : V2) b5506 e5493 e5414 (by rfl)
theorem e5495 : o1.add b5420 (List.nil : V1)=b5420 := by rfl
theorem e5496 : o2.add (List.nil : V2) b5499=b5499 := by rfl
theorem e5497 : o2.add b5506 b5507=b5498 := @add_cons V1 _ o1 b5420 (List.nil : V1) b5420 (List.nil : V2) b5499 b5499 b5498 e5495 e5496 (by rfl)
theorem e5498 : o2.mul b5459 b65=b5498 := @mul_cons V1 _ o1 b332 b5461 b65 b5499 b5506 b5507 b5498 e5492 e5494 (by rfl) e5497
theorem e5499 : o1.mul b331 b64=b5419 := by decide
theorem e5500 : o1.scale b331 b65=b5508 := @scale_cons V1 _ o1 b331 b64 b5419 (List.nil : V2) (List.nil : V2) b5508 e5499 e5421 (by rfl)
theorem e5501 : o1.add b5419 (List.nil : V1)=b5419 := by rfl
theorem e5502 : o2.add (List.nil : V2) b5498=b5498 := by rfl
theorem e5503 : o2.add b5508 b5509=b5497 := @add_cons V1 _ o1 b5419 (List.nil : V1) b5419 (List.nil : V2) b5498 b5498 b5497 e5501 e5502 (by rfl)
theorem e5504 : o2.mul b5457 b65=b5497 := @mul_cons V1 _ o1 b331 b5459 b65 b5498 b5508 b5509 b5497 e5498 e5500 (by rfl) e5503
theorem e5505 : o1.mul b330 b64=b5418 := by decide
theorem e5506 : o1.scale b330 b65=b5510 := @scale_cons V1 _ o1 b330 b64 b5418 (List.nil : V2) (List.nil : V2) b5510 e5505 e5428 (by rfl)
theorem e5507 : o1.add b5418 (List.nil : V1)=b5418 := by rfl
theorem e5508 : o2.add (List.nil : V2) b5497=b5497 := by rfl
theorem e5509 : o2.add b5510 b5511=b5496 := @add_cons V1 _ o1 b5418 (List.nil : V1) b5418 (List.nil : V2) b5497 b5497 b5496 e5507 e5508 (by rfl)
theorem e5510 : o2.mul b5455 b65=b5496 := @mul_cons V1 _ o1 b330 b5457 b65 b5497 b5510 b5511 b5496 e5504 e5506 (by rfl) e5509
theorem e5511 : o1.mul b329 b64=b5417 := by decide
theorem e5512 : o1.scale b329 b65=b5512 := @scale_cons V1 _ o1 b329 b64 b5417 (List.nil : V2) (List.nil : V2) b5512 e5511 e5435 (by rfl)
theorem e5513 : o1.add b5417 (List.nil : V1)=b5417 := by rfl
theorem e5514 : o2.add (List.nil : V2) b5496=b5496 := by rfl
theorem e5515 : o2.add b5512 b5513=b5495 := @add_cons V1 _ o1 b5417 (List.nil : V1) b5417 (List.nil : V2) b5496 b5496 b5495 e5513 e5514 (by rfl)
theorem e5516 : o2.mul b5453 b65=b5495 := @mul_cons V1 _ o1 b329 b5455 b65 b5496 b5512 b5513 b5495 e5510 e5512 (by rfl) e5515
theorem e5517 : o1.mul b328 b64=b5416 := by decide
theorem e5518 : o1.scale b328 b65=b5514 := @scale_cons V1 _ o1 b328 b64 b5416 (List.nil : V2) (List.nil : V2) b5514 e5517 e5442 (by rfl)
theorem e5519 : o1.add b5416 (List.nil : V1)=b5416 := by rfl
theorem e5520 : o2.add (List.nil : V2) b5495=b5495 := by rfl
theorem e5521 : o2.add b5514 b5515=b5494 := @add_cons V1 _ o1 b5416 (List.nil : V1) b5416 (List.nil : V2) b5495 b5495 b5494 e5519 e5520 (by rfl)
theorem e5522 : o2.mul b5451 b65=b5494 := @mul_cons V1 _ o1 b328 b5453 b65 b5495 b5514 b5515 b5494 e5516 e5518 (by rfl) e5521
theorem e5523 : o1.mul b327 b64=b5415 := by decide
theorem e5524 : o1.scale b327 b65=b5516 := @scale_cons V1 _ o1 b327 b64 b5415 (List.nil : V2) (List.nil : V2) b5516 e5523 e5449 (by rfl)
theorem e5525 : o1.add b5415 (List.nil : V1)=b5415 := by rfl
theorem e5526 : o2.add (List.nil : V2) b5494=b5494 := by rfl
theorem e5527 : o2.add b5516 b5517=b5493 := @add_cons V1 _ o1 b5415 (List.nil : V1) b5415 (List.nil : V2) b5494 b5494 b5493 e5525 e5526 (by rfl)
theorem e5528 : o2.mul b5449 b65=b5493 := @mul_cons V1 _ o1 b327 b5451 b65 b5494 b5516 b5517 b5493 e5522 e5524 (by rfl) e5527
theorem e5529 : o1.mul b326 b64=b5414 := by decide
theorem e5530 : o1.scale b326 b65=b5518 := @scale_cons V1 _ o1 b326 b64 b5414 (List.nil : V2) (List.nil : V2) b5518 e5529 e5456 (by rfl)
theorem e5531 : o1.add b5414 (List.nil : V1)=b5414 := by rfl
theorem e5532 : o2.add (List.nil : V2) b5493=b5493 := by rfl
theorem e5533 : o2.add b5518 b5519=b5492 := @add_cons V1 _ o1 b5414 (List.nil : V1) b5414 (List.nil : V2) b5493 b5493 b5492 e5531 e5532 (by rfl)
theorem e5534 : o2.mul b5447 b65=b5492 := @mul_cons V1 _ o1 b326 b5449 b65 b5493 b5518 b5519 b5492 e5528 e5530 (by rfl) e5533
theorem e5535 : o1.mul (List.nil : V1) b64=(List.nil : V1) := by rfl
theorem e5536 : o1.scale (List.nil : V1) b65=(List.nil : V2) := @scale_cons V1 _ o1 (List.nil : V1) b64 (List.nil : V1) (List.nil : V2) (List.nil : V2) (List.nil : V2) e5535 e3696 (by rfl)
theorem e5537 : o2.add (List.nil : V2) b5491=b5491 := by rfl
theorem e5538 : o2.mul b5445 b65=b5491 := @mul_cons V1 _ o1 (List.nil : V1) b5447 b65 b5492 (List.nil : V2) b5491 b5491 e5534 e5536 (by rfl) e5537
theorem e5539 : o2.add (List.nil : V2) b5490=b5490 := by rfl
theorem e5540 : o2.mul b5443 b65=b5490 := @mul_cons V1 _ o1 (List.nil : V1) b5445 b65 b5491 (List.nil : V2) b5490 b5490 e5538 e5536 (by rfl) e5539
theorem e5541 : o2.add (List.nil : V2) b5489=b5489 := by rfl
theorem e5542 : o2.mul b5441 b65=b5489 := @mul_cons V1 _ o1 (List.nil : V1) b5443 b65 b5490 (List.nil : V2) b5489 b5489 e5540 e5536 (by rfl) e5541
theorem e5543 : o2.add (List.nil : V2) b5488=b5488 := by rfl
theorem e5544 : o2.mul b5439 b65=b5488 := @mul_cons V1 _ o1 (List.nil : V1) b5441 b65 b5489 (List.nil : V2) b5488 b5488 e5542 e5536 (by rfl) e5543
theorem e5545 : o2.add (List.nil : V2) b5487=b5487 := by rfl
theorem e5546 : o2.mul b5437 b65=b5487 := @mul_cons V1 _ o1 (List.nil : V1) b5439 b65 b5488 (List.nil : V2) b5487 b5487 e5544 e5536 (by rfl) e5545
theorem e5547 : o2.add (List.nil : V2) b5424=b5424 := by rfl
theorem e5548 : o2.mul b336 b65=b5424 := @mul_cons V1 _ o1 (List.nil : V1) b5437 b65 b5487 (List.nil : V2) b5424 b5424 e5546 e5536 (by rfl) e5547
theorem e5549 : o2.mul (List.nil : V2) b67=(List.nil : V2) := by rfl

end RKResearch.Certified.Graded.NativePencilCubicDAG
