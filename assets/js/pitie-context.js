/*
 * Pitié "Contexte" timeline page logic — scroll-triggered reveal
 * animations for the timeline items and context cards.
 */
(function () {
    'use strict';

    function init() {
        const observerOptions = {
            threshold: 0.15,
            rootMargin: '0px 0px -100px 0px'
        };

        const observer = new IntersectionObserver((entries) => {
            entries.forEach((entry) => {
                if (entry.isIntersecting) {
                    entry.target.style.opacity = '1';
                    entry.target.style.transform = 'translateX(0)';
                }
            });
        }, observerOptions);

        document.querySelectorAll('.pitie-context .timeline-item').forEach((item) => {
            observer.observe(item);
        });

        document.querySelectorAll('.pitie-context .timeline-content').forEach((content) => {
            content.addEventListener('click', function () {
                this.style.background = '#f0f7ff';
                setTimeout(() => {
                    this.style.background = '#ffffff';
                }, 400);
            });
        });

        const contextCards = document.querySelectorAll('.pitie-context .context-card');
        const contextObserver = new IntersectionObserver((entries) => {
            entries.forEach((entry) => {
                if (entry.isIntersecting) {
                    entry.target.style.opacity = '1';
                    entry.target.style.transform = 'translateY(0)';
                }
            });
        }, { threshold: 0.2 });

        contextCards.forEach((card, index) => {
            card.style.opacity = '0';
            card.style.transform = 'translateY(30px)';
            card.style.transition = `all 0.6s ease ${index * 0.2}s`;
            contextObserver.observe(card);
        });
    }

    document.addEventListener('DOMContentLoaded', init);
})();
